-- Prove2me | Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_ProductExactness_PiM_pi_map_mul_right
-- name    : Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.pi_map_mul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:19:22.634333+00:00
-- url     : https://prove2.me/theorems/801d0ae4-ba60-4cd8-a5cd-5ea1c30ff0ab
-- title:
--   Pi M: pi map mul right
-- statement:
--   The Pi M construction uses the pi map mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/PiMapMulRight.lean#L63-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/PiMapMulRight.lean#L63-L75

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
variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, MeasurableSpace (G i)]
  [∀ i, MeasurableMul (G i)]

theorem Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.pi_map_mul_right (μ : ∀ i, Measure (G i)) [∀ i, SigmaFinite (μ i)] (g : ∀ i, G i)
    (h : ∀ i, (μ i).map (fun x => x * g i) = μ i) : (Measure.pi μ).map (fun x => x * g) = Measure.pi μ := by sorry
