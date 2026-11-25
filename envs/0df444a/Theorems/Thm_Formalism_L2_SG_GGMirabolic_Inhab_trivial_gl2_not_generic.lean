-- Prove2me | Theorems.Thm_Formalism_L2_SG_GGMirabolic_Inhab_trivial_gl2_not_generic
-- name    : Formalism.L2.SG.GGMirabolic.Inhab.trivial_gl2_not_generic
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:50:42.244687+00:00
-- url     : https://prove2.me/theorems/3356afc1-a312-464e-9549-2074005fdce5
-- title:
--   Inhab: trivial gl2 not generic
-- statement:
--   The Inhab construction uses the trivial gl2 not generic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GGMirabolicInhab.lean#L65-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GGMirabolicInhab.lean#L65-L74

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolicInhab
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.GGMirabolic Formalism.L2.SG.GGMirabolic.Inhab
open Formalism.L2.SG.GGMirabolic
noncomputable section
open Classical

theorem Formalism.L2.SG.GGMirabolic.Inhab.trivial_gl2_not_generic : ¬ Generic psi3 (Representation.trivial ℂ (GL (Fin 2) (ZMod 3)) ℂ) := by sorry
