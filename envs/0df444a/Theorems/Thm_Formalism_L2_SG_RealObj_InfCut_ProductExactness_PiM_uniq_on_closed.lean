-- Prove2me | Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_ProductExactness_PiM_uniq_on_closed
-- name    : Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.uniq_on_closed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:51.727301+00:00
-- url     : https://prove2.me/theorems/6885eea7-1e9d-41de-ac9c-706ab33035ce
-- title:
--   Pi M: uniq on closed
-- statement:
--   The Pi M construction uses the uniq on closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/PiMapMulRight.lean#L91-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/PiMapMulRight.lean#L91-L168

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

theorem Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.uniq_on_closed {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (hH : IsClosed (H : Set G)) (μ ν : Measure G)
    [SigmaFinite μ] [SigmaFinite ν] (hμc : μ (H : Set G)ᶜ = 0) (hνc : ν (H : Set G)ᶜ = 0)
    (hμi : ∀ h ∈ H, μ.map (fun x => h * x) = μ) (hνi : ∀ h ∈ H, ν.map (fun x => h * x) = ν) (hμ0 : μ ≠ 0)
    (hν0 : ν ≠ 0) : ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ μ = κ • ν := by sorry
