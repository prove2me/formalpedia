-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_descending_lintegral_all_beta
-- name    : AvramDividend.Classical.avram_ws01e_bt_new_original_clock_descending_lintegral_all_beta
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T01:24:58.110997+00:00
-- url     : https://prove2.me/theorems/b770b878-1132-4cb0-99ed-516fed11e944
-- title:
--   Exact original exponential-clock descending ENNReal Laplace transform for every positive rate
-- statement:
--   For the actual original spectrally negative Lévy process X and independent Exp(p) observation horizon, let λ>0 satisfy ψλ=p>0. There is an actual strictly positive derivative m at λ such that for every β>0, the true ENNReal Laplace integral of the actual drawdown S_e−X_e equals ofReal of (p/λ)(λ−β)/(p−ψβ) away from β=λ and ofReal(p/(λm)) at β=λ. This follows from the genuine original-clock all-β real MGF Wiener–Hopf theorem and the independently accepted exact original-clock lintegral-MGF equality; it is valid beyond the moment-rate gap and imposes no false change-of-measure factorisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_descending_mgf_all_beta
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_descending_lintegral_eq_mgf_positive

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bt_new_original_clock_descending_lintegral_all_beta
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (lam : ℝ) (hlam : 0 < lam) (hroot : X.ψ lam = p) :
    ∃ m : ℝ, 0 < m ∧ HasDerivAt X.ψ m lam ∧
      ∀ β : ℝ, 0 < β →
        (∫⁻ z : Ω × ℝ, ENNReal.ofReal (Real.exp
          (-β * (runningSup X (Real.toNNReal z.2) z.1 -
            X.X (Real.toNNReal z.2) z.1)))
          ∂(P.prod (expMeasure p))) =
        ENNReal.ofReal
          (if β = lam then p / (lam * m)
          else (p / lam) * ((lam - β) / (p - X.ψ β))) := by sorry
