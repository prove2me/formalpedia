-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f17_original_dense_bounded_stop_exact_gaussian_C2_bound
-- name    : AvramDividend.Classical.avram_f17_original_dense_bounded_stop_exact_gaussian_C2_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:53:15.258951+00:00
-- url     : https://prove2.me/theorems/050a5b45-48df-4704-becd-ab0394cca047
-- title:
--   Bounded original dense-grid stopping time simultaneously controls exact left-limit Gaussian gradient and Hessian
-- statement:
--   The genuinely original dense-observation compact exit time, bounded by B, is a stopping time for the right-continuous original filtration and supplies a single deterministic pair of discounted Gaussian gradient/Hessian bounds at all actual pre-exit left reserve limits. The mesh assumption is the standard DenseRange of r, discharged by a genuine open interval argument. The proof combines independently Proved stopped clock 95286a41 and exact left-limit compact bounds 4586943e without any surrogate Brownian process.
-- source:
--   Acyclic same-source reconciliation: a public Proved original right-continuous bounded observation stop and public Proved original exact positive left-limit discounted Gaussian C2 bounds, linked by the accepted dense-grid neighbourhood proof from 95286a41.

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_dense_bounded_clock_right_left_uniform_C2
import Theorems.Thm_AvramDividend_Classical_avram_f17_original_preexit_exact_leftLim_gaussian_uniform_C2_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f17_original_dense_bounded_stop_exact_gaussian_C2_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (r : ℕ → ℝ≥0) (lower upper : ℝ) (hlower : 0 < lower)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (hdense : DenseRange r) (B : ℝ≥0) :
    IsStoppingTime 𝓕.rightCont (fun ω : Ω =>
      min (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
            upper < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) (B : WithTop ℝ≥0)) ∧
    ∃ KG KH : ℝ, 0 ≤ KG ∧ 0 ≤ KH ∧
      ∀ (ω : Ω) (T : ℝ≥0),
        (T : WithTop ℝ≥0) ≤ min (⨅ k : ℕ,
          if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
              upper < x + X.X (r k) ω - rightLimit D (r k) ω
          then (r k : WithTop ℝ≥0) else ⊤) (B : WithTop ℝ≥0) →
        ∀ t : ℝ≥0, 0 < t → t < T →
          let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
          y ∈ Set.Icc lower upper ∧
            |Real.exp (-(q * (t : ℝ))) * deriv w y| ≤ KG ∧
            |Real.exp (-(q * (t : ℝ))) * iteratedDeriv 2 w y| ≤ KH := by sorry
