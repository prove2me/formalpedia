-- Prove2me | Theorems.Thm_Formalism_L2_DIV_CSD_pairOne_apply
-- name    : Formalism.L2.DIV.CSD.pairOne_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:51:34.455879+00:00
-- url     : https://prove2.me/theorems/974e9e20-c691-4a98-ac05-1e5514aba0b9
-- title:
--   CSD: pair One apply
-- statement:
--   The CSD construction uses the pair One apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ClassSumBridge.lean#L31-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ClassSumBridge.lean#L31-L31

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumBridge
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

theorem Formalism.L2.DIV.CSD.pairOne_apply (K : Type) [Field K] [StarRing K] (x y : K) : pairOne K x y = star x * y := by sorry
