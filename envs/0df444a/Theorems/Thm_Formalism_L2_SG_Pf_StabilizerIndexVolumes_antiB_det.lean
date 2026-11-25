-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_StabilizerIndexVolumes_antiB_det
-- name    : Formalism.L2.SG.Pf.StabilizerIndexVolumes.antiB_det
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:16:29.035013+00:00
-- url     : https://prove2.me/theorems/a92a741f-0169-4db2-81fa-7ecf956b5cd8
-- title:
--   Stabilizer Index Volumes: anti B det
-- statement:
--   The Stabilizer Index Volumes construction uses the anti B det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/StabilizerIndexVolumes/PtMatIsUnit.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/StabilizerIndexVolumes/PtMatIsUnit.lean#L33-L38

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

theorem Formalism.L2.SG.Pf.StabilizerIndexVolumes.antiB_det (t : K) (ht : t ≠ 0) (s : ℕ) : (antiB t s).det ≠ 0 := by sorry
