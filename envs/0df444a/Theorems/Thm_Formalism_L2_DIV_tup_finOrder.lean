-- Prove2me | Theorems.Thm_Formalism_L2_DIV_tup_finOrder
-- name    : Formalism.L2.DIV.tup_finOrder
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:48:24.790787+00:00
-- url     : https://prove2.me/theorems/be37dc20-1ffd-59f9-b930-b7ac616a9c3b
-- title:
--   DIV: tup fin Order
-- statement:
--   The DIV construction uses the tup fin Order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/TuplesLemmas.lean#L45-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/TuplesLemmas.lean#L45-L45

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Tuples
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism Formalism.L2 Formalism.L2.DIV
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {K : Type} [Field K] [NumberField K] [StarRing K] {S : Set ℕ}

theorem Formalism.L2.DIV.tup_finOrder (ξ : Tup F E K S) : IsOfFinOrder (ξ : Chr F E K) := by sorry
