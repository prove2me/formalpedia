-- Prove2me | Theorems.Thm_Formalism_L2_SG_GGMirabolic_Inhab_regular_quot
-- name    : Formalism.L2.SG.GGMirabolic.Inhab.regular_quot
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:47:36.415416+00:00
-- url     : https://prove2.me/theorems/25a01bf2-ebb2-5072-abf7-199a3b60487f
-- title:
--   Inhab: regular quot
-- statement:
--   The Inhab construction uses the regular quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GGMirabolicInhab.lean#L86-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GGMirabolicInhab.lean#L86-L87

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

theorem Formalism.L2.SG.GGMirabolic.Inhab.regular_quot {G : Type} [Group G] (i j : G) : MulOpposite.op (j⁻¹ * i) • j = i := by sorry
