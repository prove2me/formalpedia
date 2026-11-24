-- Prove2me | Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_ProductExactness_PiM_factor_uniq
-- name    : Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.factor_uniq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:04.410071+00:00
-- url     : https://prove2.me/theorems/ea30f4d6-4ca7-4afe-a92a-712e071d8c62
-- title:
--   Pi M: factor uniq
-- statement:
--   The Pi M construction uses the factor uniq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/ExistsBox.lean#L80-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/ExistsBox.lean#L80-L109

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, IsTopologicalGroup (G v)] [∀ v, SecondCountableTopology (G v)] [∀ v, MeasurableSpace (G v)]
  [∀ v, BorelSpace (G v)]

theorem Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.factor_uniq (μ : ∀ v, Measure (G v)) [∀ v, SigmaFinite (μ v)] (H : ∀ v, Subgroup (G v))
    (hH : ∀ v, IsClosed (H v : Set (G v))) (ν : ∀ v, Measure (G v)) [∀ v, SigmaFinite (ν v)]
    (hνc : ∀ v, ν v (H v : Set (G v))ᶜ = 0) (hνi : ∀ v, ∀ h ∈ H v, (ν v).map (fun x => h * x) = ν v)
    (hν0 : ∀ v, ν v ≠ 0) (h0 : Measure.pi μ ≠ 0)
    (hc : Measure.pi μ (Set.univ.pi fun v => (H v : Set (G v)))ᶜ = 0)
    (hi : ∀ g : (v : ι) → G v, (∀ v, g v ∈ H v) → (Measure.pi μ).map (fun x => g * x) = Measure.pi μ) (v : ι) :
    ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ μ v = κ • ν v := by sorry
