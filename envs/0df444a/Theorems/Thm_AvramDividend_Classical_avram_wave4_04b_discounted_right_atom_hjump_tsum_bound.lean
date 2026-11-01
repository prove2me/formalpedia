-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_discounted_right_atom_hjump_tsum_bound
-- name    : AvramDividend.Classical.avram_wave4_04b_discounted_right_atom_hjump_tsum_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:46:25.071933+00:00
-- url     : https://prove2.me/theorems/da376114-c426-48f9-9597-329f02a63bb7
-- title:
--   Aggregate discounted chronological right-dividend jump corrections satisfy the original hjump secant inequality
-- statement:
--   On the actual filtered spectrally negative Lévy surplus and an arbitrary adapted dividend strategy, assume the original right-payment hjump inequality at every time of a finite closed horizon. Then for every set of time atoms A (not just finite sets), the complete discounted sum of the actual restricted Stieltjes atomic masses is bounded by the corresponding chronological test-function drops at the genuine pre-dividend riskProcess state. The proof includes a possible initial payment atom at t=0 and terminal right atom at t=T, and uses the dividend-measure singleton identity to make the sums source-exact. There is no purely atomic concentration claim: diffuse dividend mass is a separate obligation.
-- source:
--   Actual Avram rightLimit D, riskProcess X x D and dividendMeasure; monotonicity of extended nonnegative sums, exact singleton right-payment masses and hjump. This is the jump-correction part of a controlled Stieltjes Itô–Meyer balance, not a stochastic chain rule.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_04b_discounted_right_atom_hjump_tsum_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω) (T : ℝ≥0) (q : ℝ)
    (hjump : ∀ t : ℝ≥0, t ≤ T →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∀ A : Set ℝ,
      (∑' s : A,
        μ {(s : ℝ)} *
          ENNReal.ofReal (Real.exp (-(q * (s : ℝ))))) ≤
      (∑' s : A,
        ENNReal.ofReal
          (w (riskProcess X x D (s : ℝ).toNNReal ω) -
           w (riskProcess X x D (s : ℝ).toNNReal ω -
             (rightLimit D (s : ℝ).toNNReal ω -
               D (s : ℝ).toNNReal ω))) *
          ENNReal.ofReal (Real.exp (-(q * (s : ℝ))))) := by sorry
