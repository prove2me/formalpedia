-- Prove2me | Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_ProductExactness_PiM_exists_box_alt
-- name    : Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.exists_box_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:17.162371+00:00
-- url     : https://prove2.me/theorems/03ace3ae-8cd9-4b37-9f11-916702ebfbcb
-- title:
--   Pi M: exists box alt
-- statement:
--   The Pi M construction uses the exists box alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/ExistsBox.lean#L15-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/ExistsBox.lean#L15-L28

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_PiMapMulRight
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_ExistsBox
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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)]

theorem Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.exists_box_alt (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (hne : ∀ i, μ i ≠ 0) :
    ∃ S : ∀ i, Set (α i), (∀ i, MeasurableSet (S i)) ∧ (∀ i, μ i (S i) ≠ 0) ∧ ∀ i, μ i (S i) ≠ ∞ := by sorry
