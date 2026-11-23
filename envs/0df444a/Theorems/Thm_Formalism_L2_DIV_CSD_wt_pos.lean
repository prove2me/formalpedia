-- Prove2me | Theorems.Thm_Formalism_L2_DIV_CSD_wt_pos
-- name    : Formalism.L2.DIV.CSD.wt_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:43:20.213862+00:00
-- url     : https://prove2.me/theorems/0fc33e74-e4f2-4bb0-9d1c-224a96720210
-- title:
--   CSD: wt pos
-- statement:
--   The CSD construction uses the wt pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ClassSumLemmas.lean#L56-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ClassSumLemmas.lean#L56-L56

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

theorem Formalism.L2.DIV.CSD.wt_pos (c : S.Cl) : 0 < S.wt c := by sorry
