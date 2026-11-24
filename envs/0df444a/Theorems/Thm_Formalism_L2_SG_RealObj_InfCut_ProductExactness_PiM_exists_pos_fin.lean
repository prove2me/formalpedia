-- Prove2me | Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_ProductExactness_PiM_exists_pos_fin
-- name    : Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.exists_pos_fin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:53.397162+00:00
-- url     : https://prove2.me/theorems/0a1ad4a2-ffe0-4c5a-9531-7ef66dd0117c
-- title:
--   Pi M: exists pos fin
-- statement:
--   The Pi M construction uses the exists pos fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/PiMapMulRight.lean#L81-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/PiMapMulRight.lean#L81-L89

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_LintegralFinProd
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_PiMapMulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology
open scoped ENNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.ProductExactness Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM

theorem Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.exists_pos_fin {β : Type*} [MeasurableSpace β] (ν : Measure β) [SigmaFinite ν] (h : ν ≠ 0) :
    ∃ t, MeasurableSet t ∧ ν t ≠ 0 ∧ ν t ≠ ∞ := by sorry
