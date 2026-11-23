-- Prove2me | Theorems.Thm_Formalism_L2_DIV_CSD_I_eq_sum
-- name    : Formalism.L2.DIV.CSD.I_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:58.91105+00:00
-- url     : https://prove2.me/theorems/56edd924-bf0a-4840-adaa-f7a382417987
-- title:
--   CSD: I eq sum
-- statement:
--   The CSD construction uses the I eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ClassSumLemmas.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ClassSumLemmas.lean#L30-L32

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

theorem Formalism.L2.DIV.CSD.I_eq_sum (x : Fin S.dim → K) : S.I x = ∑ i, x i • (S.basis i : S.Cl → S.V) := by sorry
