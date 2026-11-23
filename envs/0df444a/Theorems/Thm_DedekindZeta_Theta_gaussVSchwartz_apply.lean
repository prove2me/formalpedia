-- Prove2me | Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
-- name    : DedekindZeta.Theta.gaussVSchwartz_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:50:10.470399+00:00
-- url     : https://prove2.me/theorems/f15f35bd-dd44-4607-95eb-0b88fed53167
-- title:
--   Theta: gauss VSchwartz apply
-- statement:
--   The Theta construction uses the gauss VSchwartz apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1863-L1864
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Theta.lean#L1863-L1864

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section

theorem DedekindZeta.Theta.gaussVSchwartz_apply (v : minkowskiSpace K) :
    gaussVSchwartz K v = gaussV K v := by sorry

attribute [defeq] DedekindZeta.Theta.gaussVSchwartz_apply
