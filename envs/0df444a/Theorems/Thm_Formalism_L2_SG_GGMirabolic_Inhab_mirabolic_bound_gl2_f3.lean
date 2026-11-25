-- Prove2me | Theorems.Thm_Formalism_L2_SG_GGMirabolic_Inhab_mirabolic_bound_gl2_f3
-- name    : Formalism.L2.SG.GGMirabolic.Inhab.mirabolic_bound_gl2_f3
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:47:36.723982+00:00
-- url     : https://prove2.me/theorems/9dc12465-516e-5c6f-98e6-1e2b612f985f
-- title:
--   Inhab: mirabolic bound gl2 f3
-- statement:
--   The Inhab construction uses the mirabolic bound gl2 f3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GGMirabolicInhab.lean#L76-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GGMirabolicInhab.lean#L76-L79

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

theorem Formalism.L2.SG.GGMirabolic.Inhab.mirabolic_bound_gl2_f3 : ∏ i ∈ Finset.Ico 1 2, (Fintype.card (ZMod 3) ^ i - 1) = 2 ∧
    Module.finrank ℂ ℂ = 1 := by sorry
