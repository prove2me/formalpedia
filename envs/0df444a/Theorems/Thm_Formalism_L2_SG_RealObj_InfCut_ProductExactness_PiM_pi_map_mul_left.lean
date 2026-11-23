-- Prove2me | Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_ProductExactness_PiM_pi_map_mul_left
-- name    : Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.pi_map_mul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:19:13.693014+00:00
-- url     : https://prove2.me/theorems/1b31eae4-572d-44d7-91ea-458bc5e2b45c
-- title:
--   Pi M: pi map mul left
-- statement:
--   The Pi M construction uses the pi map mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/PiMapMulRight.lean#L49-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/PiMapMulRight.lean#L49-L61

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

theorem Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.pi_map_mul_left (μ : ∀ i, Measure (G i)) [∀ i, SigmaFinite (μ i)] (g : ∀ i, G i)
    (h : ∀ i, (μ i).map (fun x => g i * x) = μ i) : (Measure.pi μ).map (fun x => g * x) = Measure.pi μ := by sorry
