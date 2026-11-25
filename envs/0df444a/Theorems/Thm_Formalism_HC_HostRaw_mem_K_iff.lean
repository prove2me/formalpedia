-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_mem_K_iff
-- name    : Formalism.HC.HostRaw.mem_K_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:26:02.802032+00:00
-- url     : https://prove2.me/theorems/b21d4358-0f4b-4e40-a7b9-615ec77d5296
-- title:
--   Host Raw: mem K iff
-- statement:
--   The Host Raw construction uses the mem K iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/AdjoinCycZeta.lean#L68-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/AdjoinCycZeta.lean#L68-L73

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_AdjoinCycZeta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IntermediateField NumberField
open Formalism Formalism.HC Formalism.HC.HostRaw
open Formalism.FrobeniusOrbits Formalism.L2.Host
variable {φ : Frame} (H : HostRaw φ)

theorem Formalism.HC.HostRaw.mem_K_iff (j : H.E →ₐ[ℚ] Qb) (x : H.E) : x ∈ H.K ↔ j x ∈ KQ H.d := by sorry
