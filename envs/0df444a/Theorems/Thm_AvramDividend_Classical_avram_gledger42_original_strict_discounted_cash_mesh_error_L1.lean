-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger42_original_strict_discounted_cash_mesh_error_L1
-- name    : AvramDividend.Classical.avram_gledger42_original_strict_discounted_cash_mesh_error_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T19:54:00.009347+00:00
-- url     : https://prove2.me/theorems/ad2796e6-b82b-497d-9001-2b293a6dae05
-- title:
--   Original strict discounted bounded-clock mesh discount and last-cell errors vanish in L1
-- statement:
--   For a bounded stopping clock on the original filtered probability space, the physical-grid correction qΔ exp(qn) times actual strict discounted pre-clock dividend cash, plus strict discounted open-last-cell cash, is integrable with arbitrarily small expectation. The exponential factor makes the discount correction dominate the unweighted mass error, since times lie in the bounded horizon. This repairs the measurability and L1 gap of a raw unweighted random measure without an auxiliary process. The mesh uses n/(m+2), a successor-index reparameterisation of n/(m+1).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gledger42_original_strict_discounted_cash_mesh_error_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0)) :
    let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 2)
      let F : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      let T : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
            Ioo ((ρ ω : ℝ) - Δ) (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      q * Δ * Real.exp (q * (n : ℝ)) * F + T
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (E m) P ∧ (∫ ω, E m ω ∂P) ≤ ε := by sorry
