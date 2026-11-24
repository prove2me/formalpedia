-- Prove2me | Theorems.Thm_Formalism_HC_HostRaw_aut_mem_F
-- name    : Formalism.HC.HostRaw.aut_mem_F
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:24:00.510566+00:00
-- url     : https://prove2.me/theorems/97d6836c-42a4-4337-8fdf-87b5181afaf6
-- title:
--   Host Raw: aut mem F
-- statement:
--   The Host Raw construction uses the aut mem F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/AdjoinCycZeta.lean#L48-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/AdjoinCycZeta.lean#L48-L49

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

theorem Formalism.HC.HostRaw.aut_mem_F (σ : H.E ≃ₐ[ℚ] H.E) {x : H.E} (hx : x ∈ H.F) : σ x ∈ H.F := by sorry
