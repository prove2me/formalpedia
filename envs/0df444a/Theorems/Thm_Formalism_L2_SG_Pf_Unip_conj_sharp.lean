-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_Unip_conj_sharp
-- name    : Formalism.L2.SG.Pf.Unip.conj_sharp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:23.685165+00:00
-- url     : https://prove2.me/theorems/68a95204-1a3a-4839-a0b3-2f07d27d9be1
-- title:
--   Unip: conj sharp
-- statement:
--   The Unip construction uses the conj sharp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RCocompactPfConj.lean#L40-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RCocompactPfConj.lean#L40-L53

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RCocompactPfConj
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Unip
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [StarRing K]

theorem Formalism.L2.SG.Pf.Unip.conj_sharp {J J' G G' A : Matrix ι ι K} (hJh : Jᴴ = J) (hJ'h : J'ᴴ = J') (hJ : J' * J = 1) (hJ' : J * J' = 1)
    (hG : Gᴴ * J * G = J) (h : G * G' = 1) : G' * sharp J J' A * G = sharp J J' (G' * A * G) := by sorry
