-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_jOf_coe
-- name    : Formalism.HC.HostRaw.jOf_coe
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:24:42.756994+00:00
-- url     : https://prove2.me/theorems/ac5c3eda-5b81-4e02-a305-307b6a848336
-- title:
--   Host Raw: j Of coe
-- statement:
--   The Host Raw construction uses the j Of coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/AdjoinCycZeta.lean#L92-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/AdjoinCycZeta.lean#L92-L92

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_AdjoinCycZeta
import Theorems.Thm_Formalism_L2_Host_jOf_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Host.jOf_coe


set_option autoImplicit false
noncomputable section
open IntermediateField NumberField
open Formalism Formalism.HC Formalism.HC.HostRaw
open Formalism.FrobeniusOrbits Formalism.L2.Host
variable {φ : Frame} (H : HostRaw φ)

theorem Formalism.HC.HostRaw.jOf_coe (j : H.E →ₐ[ℚ] Qb) (x : H.E) : ((H.jOf j x : H.EQ) : Qb) = j x := by sorry

attribute [defeq] Formalism.HC.HostRaw.jOf_coe
