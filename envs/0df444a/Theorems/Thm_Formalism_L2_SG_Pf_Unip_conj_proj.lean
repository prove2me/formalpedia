-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_Unip_conj_proj
-- name    : Formalism.L2.SG.Pf.Unip.conj_proj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:17:48.194643+00:00
-- url     : https://prove2.me/theorems/aa143c9f-6242-484d-b194-eb859fdaf1a3
-- title:
--   Unip: conj proj
-- statement:
--   The Unip construction uses the conj proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RCocompactPfConj.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/RCocompactPfConj.lean#L55-L59

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

theorem Formalism.L2.SG.Pf.Unip.conj_proj [Invertible (2 : K)] {J J' G G' A : Matrix ι ι K} (hJh : Jᴴ = J) (hJ'h : J'ᴴ = J')
    (hJ : J' * J = 1) (hJ' : J * J' = 1) (hG : Gᴴ * J * G = J) (h : G * G' = 1) :
    G' * proj J J' A * G = proj J J' (G' * A * G) := by sorry
