-- Prove2me | Theorems.Thm_Formalism_L2_DIV_sqrts_sub
-- name    : Formalism.L2.DIV.sqrts_sub
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:31:41.356945+00:00
-- url     : https://prove2.me/theorems/50d0f4a0-c5d3-4e97-9eab-d5de0f1c9ee1
-- title:
--   DIV: sqrts sub
-- statement:
--   The DIV construction uses the sqrts sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoeffLemmas.lean#L28-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoeffLemmas.lean#L28-L28

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ConjugationAtDistinguishedPlace
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoeffLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.L2.Host Formalism.DivisionValues

theorem Formalism.L2.DIV.sqrts_sub (m : ℤ) : sqrts m ⊆ (sqQ m : Set Qb) := by sorry
