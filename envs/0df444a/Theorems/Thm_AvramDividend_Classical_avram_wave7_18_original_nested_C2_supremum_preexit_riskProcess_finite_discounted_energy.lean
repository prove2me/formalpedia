-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_nested_C2_supremum_preexit_riskProcess_finite_discounted_energy
-- name    : AvramDividend.Classical.avram_wave7_18_original_nested_C2_supremum_preexit_riskProcess_finite_discounted_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:35:33.897675+00:00
-- url     : https://prove2.me/theorems/1bad97a6-8a1d-4723-a19c-2ac9835aef26
-- title:
--   Finite discounted original riskProcess C2-jet energy before the supremum of nested source stopping clocks
-- statement:
--   For nested original-filtration dense-grid first-exit stopping clocks in source positive C2 bands and nondecreasing deterministic time bounds, any finite time strictly below the pointwise supremum of the clocks lies before one finite-stage source stopping time by lt_iSup_iff. Under q>0 and the exact ContDiffOn ℝ 2 w {y|0<y ∧ ENNReal.ofReal y<C} binder, the Proved source-specific discounted finite-energy theorem supplies a deterministic stage-dependent jet bound. Consequently on every original path, before any such T, the sum of the absolute discounted w, deriv w, and deriv (deriv w) terms of the genuine pre-right-payment riskProcess is ENNReal Lebesgue-integrable over every measurable finite-volume time set contained in [0,T). Neither the bound nor the martingale integrability is claimed uniform in all stages, and the theorem does not replace separate jump compensator or boundary occupation proofs.

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_discounted_riskProcess_preexit_C2_jet_finite_lebesgue_energy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_18_original_nested_C2_supremum_preexit_riskProcess_finite_discounted_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 < q)
    (r : ℕ → ℝ≥0) (hdense : DenseRange r)
    (lower upper : ℕ → ℝ) (B : ℕ → ℝ≥0)
    (hlower : ∀ n, 0 < lower n)
    (hband : ∀ n, lower n ≤ upper n)
    (hlo : ∀ n, lower (n + 1) ≤ lower n)
    (hup : ∀ n, upper n ≤ upper (n + 1))
    (hcap : ∀ n, ∀ y ∈ Set.Icc (lower n) (upper n), ENNReal.ofReal y < C)
    (hB : ∀ n, B n ≤ B (n + 1)) :
    let τ : ℕ → Ω → WithTop ℝ≥0 := fun n ω =>
      min (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower n ∨
            upper n < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) (B n : WithTop ℝ≥0)
    ∀ (ω : Ω) (T : ℝ≥0), (T : WithTop ℝ≥0) < ⨆ n, τ n ω →
      ∃ (n : ℕ) (M : ℝ), 0 ≤ M ∧
        (T : WithTop ℝ≥0) ≤ τ n ω ∧
        ∀ (A : Set ℝ), MeasurableSet A →
          (volume : Measure ℝ) A < ⊤ →
          (∀ t ∈ A, 0 ≤ t ∧ t.toNNReal < T) →
          let E : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal
            (|Real.exp (-(q * (t.toNNReal : ℝ))) *
                w (riskProcess X x D t.toNNReal ω)| +
              |Real.exp (-(q * (t.toNNReal : ℝ))) *
                deriv w (riskProcess X x D t.toNNReal ω)| +
              |Real.exp (-(q * (t.toNNReal : ℝ))) *
                deriv (deriv w) (riskProcess X x D t.toNNReal ω)|)
          (∫⁻ t : ℝ, A.indicator E t ∂(volume : Measure ℝ)) < ⊤ := by sorry
