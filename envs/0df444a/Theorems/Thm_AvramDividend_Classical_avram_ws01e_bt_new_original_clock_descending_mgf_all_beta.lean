-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_descending_mgf_all_beta
-- name    : AvramDividend.Classical.avram_ws01e_bt_new_original_clock_descending_mgf_all_beta
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T01:19:49.278098+00:00
-- url     : https://prove2.me/theorems/892680b1-98be-453e-99c3-1ca5515333b8
-- title:
--   Complete original exponential-clock descending Wiener–Hopf real MGF at every positive parameter
-- statement:
--   For any genuine original spectrally negative Lévy process, an independent Exp(p) clock, and a positive root λ with ψ(λ)=p>0, there exists a strictly positive actual derivative m=ψ′(λ) such that for every β>0, the MGF of the negative terminal drawdown S_e−X_e is (p/λ)(λ−β)/(p−ψ(β)) away from β=λ and equals the removable value p/(λ m) at β=λ. This uses the source-faithful original-clock finite positive-root MGF strip, original-clock negative-drawdown MGF analyticity, native Lévy exponent analyticity, actual differentiability and derivative positivity at the positive root, root uniqueness, and the already accepted analytic-continuation theorem. It imposes no false factorisation, extra integrability or differentiability premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_descending_real_finite_strip
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_drawdown_mgf_analytic_positive
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_levy_psi_analytic_on_positive
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_cr_new_levy_psi_hasDerivAt_positive
import Theorems.Thm_AvramDividend_Classical_esscher_levy_positive_root_derivative_lower
import Theorems.Thm_AvramDividend_Classical_levy_psi_positive_q_root_unique
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_all_beta_wh_analytic_continuation_with_removable_root

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bt_new_original_clock_descending_mgf_all_beta
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (lam : ℝ) (hlam : 0 < lam) (hroot : X.ψ lam = p) :
    ∃ m : ℝ, 0 < m ∧ HasDerivAt X.ψ m lam ∧
      ∀ β : ℝ, 0 < β →
        mgf (fun z : Ω × ℝ =>
          -(runningSup X (Real.toNNReal z.2) z.1 -
            X.X (Real.toNNReal z.2) z.1))
          (P.prod (expMeasure p)) β =
        if β = lam then p / (lam * m)
        else (p / lam) * ((lam - β) / (p - X.ψ β)) := by sorry
