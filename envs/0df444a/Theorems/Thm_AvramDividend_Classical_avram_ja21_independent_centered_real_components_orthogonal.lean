-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja21_independent_centered_real_components_orthogonal
-- name    : AvramDividend.Classical.avram_ja21_independent_centered_real_components_orthogonal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T15:00:17.28277+00:00
-- url     : https://prove2.me/theorems/07b1ffd5-0d8d-4534-93da-d23e0cdb14ec
-- title:
--   Independent centered real random variables have zero cross moment on their actual measure
-- statement:
--   Two independent real-valued random variables which are strongly measurable almost everywhere and centered under the same measure have zero expected product. This is the exact algebraic implication needed after proving original Gaussian/jump component independence and centering, without any auxiliary probability space.
-- source:
--   J-A21 generic orthogonality lemma using pinned Mathlib ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral.

import Mathlib
open MeasureTheory ProbabilityTheory
noncomputable section

theorem AvramDividend.Classical.avram_ja21_independent_centered_real_components_orthogonal
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (G J : Ω → ℝ)
    (hIndep : ProbabilityTheory.IndepFun G J P)
    (hGMeas : AEStronglyMeasurable G P)
    (hJMeas : AEStronglyMeasurable J P)
    (hGzero : (∫ ω, G ω ∂P) = 0)
    (hJzero : (∫ ω, J ω ∂P) = 0) :
    (∫ ω, G ω * J ω ∂P) = 0 := by sorry
