-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_independent_real_mgf_crossmul
-- name    : AvramDividend.Classical.avram_ws01e_bf_new_independent_real_mgf_crossmul
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:10:32.942071+00:00
-- url     : https://prove2.me/theorems/d2fe95c5-7e88-4263-a61f-47206a1affa4
-- title:
--   Independent supremum and drawdown MGFs give the finite-rate cross-multiplied factor
-- statement:
--   If the genuine supremum S and drawdown D are independent under one measure, if S has exponential moment lam/(lam-beta), and if their difference has terminal moment p/(p-gp) in the strict rate gap, then the negative-drawdown MGF satisfies (p-gp) lam L(beta) = p(lam-beta). This is purely finite-rate factorisation algebra and is used only where both positive moments are finite. It does not extend the divergent terminal MGF beyond beta<lam, nor assume the final Wiener-Hopf quotient.
-- source:
--   Finite-rate Wiener–Hopf factorisation algebra; pinned Mathlib ProbabilityTheory.IndepFun.neg_right and ProbabilityTheory.IndepFun.mgf_add. Inputs correspond to genuine Qp terminal moments and Exp(lam) supremum law; source independent of any analytic continuation assumption.

import Mathlib
import Mathlib.Probability.Moments.Basic
import Definitions.Def_AvramDividend_Classical_Reflection

open AvramDividend.Classical MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bf_new_independent_real_mgf_crossmul
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    (S D : Ω → ℝ) (p lam β gp : ℝ)
    (hIndep : ProbabilityTheory.IndepFun S D μ)
    (hS : Measurable S) (hD : Measurable D)
    (hGap : gp < p) (hLamGap : β < lam)
    (hSup : ProbabilityTheory.mgf S μ β = lam / (lam - β))
    (hTerm : ProbabilityTheory.mgf (fun ω => S ω - D ω) μ β =
      p / (p - gp)) :
    (p - gp) * lam *
      ProbabilityTheory.mgf (fun ω => -D ω) μ β =
    p * (lam - β) := by sorry
