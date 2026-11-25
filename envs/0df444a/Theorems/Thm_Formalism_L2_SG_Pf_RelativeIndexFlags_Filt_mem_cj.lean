-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RelativeIndexFlags_Filt_mem_cj
-- name    : Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.mem_cj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:44:56.551803+00:00
-- url     : https://prove2.me/theorems/0a3e9813-bfa6-52fa-ad57-71be1156da83
-- title:
--   Filt: mem cj
-- statement:
--   The Filt construction uses the mem cj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RelativeIndexFlags/RelIndexEqIndexOfMul.lean#L73-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RelativeIndexFlags/RelIndexEqIndexOfMul.lean#L73-L74

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_RelIndexEqIndexOfMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RelativeIndexFlags Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
variable {G : Type*} [Group G]

theorem Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.mem_cj (g : G) (A : Subgroup G) (y : G) : y ∈ cj g A ↔ ∃ x ∈ A, g * x * g⁻¹ = y := by sorry
