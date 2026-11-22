-- Prove2me | Theorems.Thm_Formalism_L2_DIV_CSD_I_apply
-- name    : Formalism.L2.DIV.CSD.I_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:36:11.227206+00:00
-- url     : https://prove2.me/theorems/e6b9e460-fda6-4625-9765-26d766d781fc
-- title:
--   CSD: I apply
-- statement:
--   The CSD construction uses the I apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ClassSumLemmas.lean#L16-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ClassSumLemmas.lean#L16-L16

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSum
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV Formalism.L2.DIV.CSD
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)

theorem Formalism.L2.DIV.CSD.I_apply (x : Fin S.dim → K) : S.I x = ((S.basis.equivFun.symm x : S.Forms) : S.Cl → S.V) := by sorry
