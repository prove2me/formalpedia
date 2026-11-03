-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_stopped_discounted_all_atoms_diffuse_cash_bound
-- name    : AvramDividend.Classical.avram_wave6_05_actual_original_stopped_discounted_all_atoms_diffuse_cash_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:23:37.984569+00:00
-- url     : https://prove2.me/theorems/0a519d31-606f-4fcd-a0e5-3a4f1b6fe354
-- title:
--   Exact ruin-stopped original discounted right-atom plus diffuse cash split with closed-horizon bound
-- statement:
--   For every original finite-variation dividend control, sample path and horizon T, the actual original dividendMeasure restricted to [0,T] splits exactly into its exhaustive countable original right-atomic cash and genuine atomless cash after filtering by the literal paymentTimes(ruinTime) convention. Time zero is retained and payments at a strictly positive ruin instant are excluded, including when the original spectrally negative Levy source jumps simultaneously. The full stopped discounted Stieltjes cash is bounded by ENNReal.ofReal(rightLimit D T ω) for q≥0. All continuous and singular-continuous pre-ruin cash remains in the actual atomless integral. No finite-jump or smooth-control assumption is introduced; this supplies Chat 06 a stopped cash identity without asserting the stochastic Ito–Meyer formula.
-- source:
--   Instantiate the canonical exact all-atomic-plus-atomless original Stieltjes identity for arbitrary ENNReal weight with the actual paymentTimes(ruinTime) indicator of exp(-q t). This preserves the same all-singleton support, exact rightLimit payment atoms and genuine atomless remainder. Monotonicity of ENNReal lintegrals shows the stopped discounted cash is no larger than the corresponding full-horizon discounted cash; then use the canonical original Stieltjes closed-horizon budget for q≥0. No measurability of the indicator is required for the lower-integral algebra, and no simplification of endpoint or ruin conventions is made.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_full_stieltjes_weighted_all_atoms_plus_atomless_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical

theorem AvramDividend.Classical.avram_wave6_05_actual_original_stopped_discounted_all_atoms_diffuse_cash_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      NullSingletonClass μdiffuse ∧
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      (∀ s : ℝ, μ {s} ≠ 0 → s ∈ A) ∧
      ((∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω) then
          ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂μ) =
        (∑' t : A, μ {(t : ℝ)} * (if (t : ℝ) ∈ paymentTimes (ruinTime X x D ω) then
            ENNReal.ofReal (Real.exp (-(q * (t : ℝ)))) else 0)) +
        (∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω) then
          ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂μdiffuse)) ∧
      ((∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω) then
          ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂μ) ≤
        ENNReal.ofReal (rightLimit D T ω)) := by sorry
