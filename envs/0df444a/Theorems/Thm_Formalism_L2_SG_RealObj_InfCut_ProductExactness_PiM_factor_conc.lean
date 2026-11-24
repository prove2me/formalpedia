-- Prove2me | Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_ProductExactness_PiM_factor_conc
-- name    : Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.factor_conc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:08.906175+00:00
-- url     : https://prove2.me/theorems/96fd93cc-1739-4ff1-b940-e2811d47eddf
-- title:
--   Pi M: factor conc
-- statement:
--   The Pi M construction uses the factor conc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/ExistsBox.lean#L50-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/ExistsBox.lean#L50-L64

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

theorem Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.factor_conc (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (hne : ∀ i, μ i ≠ 0) (N : ∀ i, Set (α i))
    (hc : Measure.pi μ (Set.univ.pi N)ᶜ = 0) (v : ι) : μ v (N v)ᶜ = 0 := by sorry
