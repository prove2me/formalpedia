-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_StabilizerIndexVolumes_antiB_sq
-- name    : Formalism.L2.SG.Pf.StabilizerIndexVolumes.antiB_sq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:16:34.536321+00:00
-- url     : https://prove2.me/theorems/5aa58b55-93d3-47a0-8fc4-3fa2d2166d53
-- title:
--   Stabilizer Index Volumes: anti B sq
-- statement:
--   The Stabilizer Index Volumes construction uses the anti B sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/StabilizerIndexVolumes/PtMatIsUnit.lean#L14-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/StabilizerIndexVolumes/PtMatIsUnit.lean#L14-L31

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_Point
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_StabilizerIndexVolumes_PtMatIsUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.StabilizerIndexVolumes
variable {K : Type*} [Field K]

theorem Formalism.L2.SG.Pf.StabilizerIndexVolumes.antiB_sq (t : K) (s : ℕ) : antiB t s * antiB t s = (t * t) • (1 : Matrix (Fin s) (Fin s) K) := by sorry
