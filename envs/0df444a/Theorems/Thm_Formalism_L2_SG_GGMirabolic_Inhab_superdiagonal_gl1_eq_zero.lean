-- Prove2me | Theorems.Thm_Formalism_L2_SG_GGMirabolic_Inhab_superdiagonal_gl1_eq_zero
-- name    : Formalism.L2.SG.GGMirabolic.Inhab.superdiagonal_gl1_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:37.37062+00:00
-- url     : https://prove2.me/theorems/d792fd40-b918-4b34-b092-7984afa5e9d8
-- title:
--   Inhab: superdiagonal gl1 eq zero
-- statement:
--   The Inhab construction uses the superdiagonal gl1 eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GGMirabolicInhab.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GGMirabolicInhab.lean#L44-L45

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

theorem Formalism.L2.SG.GGMirabolic.Inhab.superdiagonal_gl1_eq_zero (x : Matrix (Fin 1) (Fin 1) (ZMod 3)) : superdiag 1 x = 0 := by sorry
