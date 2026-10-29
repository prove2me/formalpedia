-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_centered_infimum_lintegral_all_beta
-- name    : AvramDividend.Classical.avram_ws01e_bt_new_original_clock_centered_infimum_lintegral_all_beta
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T01:33:29.816733+00:00
-- url     : https://prove2.me/theorems/b9a81479-f363-4c22-9035-39ae264a5800
-- title:
--   Original-clock centred running-infimum Laplace transform for every positive rate
-- statement:
--   For an actual spectrally negative Lévy process with independent Exp(p) horizon and positive root lambda of psi(lambda)=p, the complete ENNReal Laplace transform of the centred negative running infimum X_0−inf_{s≤e}X_s is exactly (p/lambda)(lambda−beta)/(p−psi(beta)) at every positive beta away from lambda, and p/(lambda*m) at the removable root where m=psi'(lambda)>0. This transports the already accepted original-clock all-beta drawdown transform through the truly Borel marginal reversal and avoids introducing any fictitious Esscher independent clock or zero-start assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_descending_lintegral_all_beta
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_drawdown_infimum_all_borel_reward

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bt_new_original_clock_centered_infimum_lintegral_all_beta
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (lam : ℝ) (hlam : 0 < lam) (hroot : X.ψ lam = p) :
    ∃ m : ℝ, 0 < m ∧ HasDerivAt X.ψ m lam ∧
      ∀ β : ℝ, 0 < β →
        (∫⁻ z : Ω × ℝ, ENNReal.ofReal (Real.exp
          (-β * (X.X 0 z.1 +
            -sInf {y : ℝ | ∃ s : ℝ≥0,
              s ≤ z.2.toNNReal ∧ y = X.X s z.1})))
          ∂(P.prod (expMeasure p))) =
        ENNReal.ofReal
          (if β = lam then p / (lam * m)
          else (p / lam) * ((lam - β) / (p - X.ψ β))) := by sorry
