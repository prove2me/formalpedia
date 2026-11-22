-- Prove2me | Theorems.Thm_Formalism_L2_DIV_CSD_csum_sum
-- name    : Formalism.L2.DIV.CSD.csum_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:46:30.251088+00:00
-- url     : https://prove2.me/theorems/72a04453-2aac-454d-ba6d-6a6f02329043
-- title:
--   CSD: csum sum
-- statement:
--   The CSD construction uses the csum sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ClassSumLemmas.lean#L34-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ClassSumLemmas.lean#L34-L45

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

theorem Formalism.L2.DIV.CSD.csum_sum (x y : Fin S.dim → K) :
    S.csum (S.I x) (S.I y) = ∑ i, ∑ j, star (x i) * S.H i j * y j := by sorry
