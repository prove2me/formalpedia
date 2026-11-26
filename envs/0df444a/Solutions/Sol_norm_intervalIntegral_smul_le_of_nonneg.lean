-- Prove2me | solution 1 for norm_intervalIntegral_smul_le_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:36:12.584869+00:00
-- url     : https://prove2.me/submissions/789acc93-fbcb-41cc-8268-9202c04670e8

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_Operator_Crouzeix_PositiveKernelBound
import Theorems.Thm_norm_intervalIntegral_smul_le_of_ae_nonneg

set_option autoImplicit false
open ContinuousLinearMap MeasureTheory
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution {K : ℝ → E →L[ℂ] E} {f : ℝ → ℂ} {a b c M : ℝ}
    (hab : a ≤ b) (hK : IntervalIntegrable K volume a b)
    (hfK : IntervalIntegrable (fun t => f t • K t) volume a b)
    (hpos : ∀ t ∈ Set.Ioc a b, 0 ≤ K t)
    (hnorm : ∫ t in a..b, K t = c • (1 : E →L[ℂ] E))
    (hc : 0 ≤ c) (hM : 0 ≤ M) (hf : ∀ t ∈ Set.Ioc a b, ‖f t‖ ≤ M) :
    ‖∫ t in a..b, f t • K t‖ ≤ c * M :=
  norm_intervalIntegral_smul_le_of_ae_nonneg hab hK hfK
    ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => hpos t ht) hnorm hc hM
    ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => hf t ht)
