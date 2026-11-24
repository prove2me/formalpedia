-- Prove2me | Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_ProductExactness_PiM_lintegral_fin_prod
-- name    : Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.lintegral_fin_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:56.984476+00:00
-- url     : https://prove2.me/theorems/b22ef4f1-6a66-4a73-81d3-6dda875f2052
-- title:
--   Pi M: lintegral fin prod
-- statement:
--   The Pi M construction uses the lintegral fin prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/LintegralFinProd.lean#L10-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/LintegralFinProd.lean#L10-L33

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_LintegralFinProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.ProductExactness Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM

theorem Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.lintegral_fin_prod : ∀ (m : ℕ) {α : Fin m → Type} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] (f : ∀ i, α i → ℝ≥0∞), (∀ i, Measurable (f i)) →
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i
  := by sorry
