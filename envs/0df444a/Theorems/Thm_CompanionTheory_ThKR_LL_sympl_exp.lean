-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_LL_sympl_exp
-- name    : CompanionTheory.ThKR.LL.sympl_exp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:01.631091+00:00
-- url     : https://prove2.me/theorems/cc51e23b-7f60-4dfe-ac14-8ef2dfb24325
-- title:
--   LL: sympl exp
-- statement:
--   The LL construction uses the sympl exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/LocalLift.lean#L55-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/LocalLift.lean#L55-L69

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_NormExpSubLe
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_LocalLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.LL
variable {l : Type} [Fintype l] [DecidableEq l]

theorem CompanionTheory.ThKR.LL.sympl_exp {X : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) (w w' : l ⊕ l → ℝ) :
    sympl (NormedSpace.exp X *ᵥ w) (NormedSpace.exp X *ᵥ w') = sympl w w' := by sorry
