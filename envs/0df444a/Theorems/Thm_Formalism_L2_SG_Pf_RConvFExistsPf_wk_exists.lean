-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RConvFExistsPf_wk_exists
-- name    : Formalism.L2.SG.Pf.RConvFExistsPf.wk_exists
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:13.017731+00:00
-- url     : https://prove2.me/theorems/930bbc22-554a-459d-8779-54b4763d3b3f
-- title:
--   RConv FExists Pf: wk exists
-- statement:
--   The RConv FExists Pf construction uses the wk exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/RConvFExistsPfAbs.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/RConvFExistsPfAbs.lean#L53-L59

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RConvFExistsPfAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RConvFExistsPf
open MeasureTheory
open scoped InnerProductSpace
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem Formalism.L2.SG.Pf.RConvFExistsPf.wk_exists {U : α → (E →L[ℂ] E)} (hU : ∀ g z, ‖U g z‖ ≤ ‖z‖)
    (hm : ∀ x y : E, AEStronglyMeasurable (fun g => ⟪x, U g y⟫_ℂ) μ) {f : α → ℂ} (hf : Integrable f μ) :
    ∃ T : E →L[ℂ] E, ∀ x y : E, ⟪x, T y⟫_ℂ = ∫ g, f g * ⟪x, U g y⟫_ℂ ∂μ := by sorry
