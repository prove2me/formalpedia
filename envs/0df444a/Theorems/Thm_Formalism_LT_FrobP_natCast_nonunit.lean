-- Prove2me | Theorems.Thm_Formalism_LT_FrobP_natCast_nonunit
-- name    : Formalism.LT.FrobP.natCast_nonunit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:53.112962+00:00
-- url     : https://prove2.me/theorems/0b3f380e-0628-421b-b3a5-f2998f71e13d
-- title:
--   Frob P: nat Cast nonunit
-- statement:
--   The Frob P construction uses the nat Cast nonunit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MemSpanOfNormLe.lean#L58-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MemSpanOfNormLe.lean#L58-L73

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

theorem Formalism.LT.FrobP.natCast_nonunit {p : ℕ} (hp : ‖(p : K)‖ < 1) :
    ((p : ℕ) : unitBall K) ∈ nonunits (unitBall K) := by sorry
