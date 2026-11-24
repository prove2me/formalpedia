-- Prove2me | Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_ProductExactness_PiM_factor_eq
-- name    : Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.factor_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:55.889663+00:00
-- url     : https://prove2.me/theorems/5559c3b6-2760-4fba-944f-d8b28d34ea4a
-- title:
--   Pi M: factor eq
-- statement:
--   The Pi M construction uses the factor eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/ExistsBox.lean#L37-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/ExistsBox.lean#L37-L48

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

theorem Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.factor_eq (μ μ' : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (μ' i)]
    (hne : ∀ i, μ i ≠ 0) (v : ι) (hw : ∀ w, w ≠ v → μ' w = μ w) (h : Measure.pi μ' = Measure.pi μ) : μ' v = μ v := by sorry
