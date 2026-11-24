-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_mem_F_iff
-- name    : Formalism.HC.HostRaw.mem_F_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:24:45.514884+00:00
-- url     : https://prove2.me/theorems/c21c63b5-d49c-4ba0-8257-51d0556914af
-- title:
--   Host Raw: mem F iff
-- statement:
--   The Host Raw construction uses the mem F iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/AdjoinCycZeta.lean#L57-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/AdjoinCycZeta.lean#L57-L62

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

theorem Formalism.HC.HostRaw.mem_F_iff (j : H.E →ₐ[ℚ] Qb) (x : H.E) : x ∈ H.F ↔ j x ∈ H.FQ := by sorry
