-- Prove2me | Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_ProductExactness_PiM_pi_ne_zero
-- name    : Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.pi_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:19:10.526086+00:00
-- url     : https://prove2.me/theorems/d8629bee-cda3-4476-85f0-1787617cdab2
-- title:
--   Pi M: pi ne zero
-- statement:
--   The Pi M construction uses the pi ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/PiMapMulRight.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/PiMapMulRight.lean#L35-L40

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
variable {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)]

theorem Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.pi_ne_zero (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (h : ∀ i, μ i ≠ 0) : Measure.pi μ ≠ 0 := by sorry
