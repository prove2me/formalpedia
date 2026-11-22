-- Prove2me | Theorems.Thm_Formalism_LT_FrobP_natCast_coe
-- name    : Formalism.LT.FrobP.natCast_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:57:03.07915+00:00
-- url     : https://prove2.me/theorems/6cbddc92-9bfd-4a2f-a6a6-c06cabffea42
-- title:
--   Frob P: nat Cast coe
-- statement:
--   The Frob P construction uses the nat Cast coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MemSpanOfNormLe.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MemSpanOfNormLe.lean#L30-L33

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v
open Formalism Formalism.LT Formalism.LT.FrobP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.LT.FrobP.natCast_coe (p : ℕ) : (((p : unitBall K)) : K) = (p : K) := by sorry
