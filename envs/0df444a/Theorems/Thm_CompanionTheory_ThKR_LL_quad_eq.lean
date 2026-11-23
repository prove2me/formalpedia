-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_LL_quad_eq
-- name    : CompanionTheory.ThKR.LL.quad_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:30:40.318063+00:00
-- url     : https://prove2.me/theorems/448ad79e-db3f-4bfe-9a26-2ebcd4406a92
-- title:
--   LL: quad eq
-- statement:
--   The LL construction uses the quad eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/LocalLift.lean#L113-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/LocalLift.lean#L113-L140

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

theorem CompanionTheory.ThKR.LL.quad_eq {X : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) (f : Sch l) :
    quad X f = mq (bl Sum.inr Sum.inl X) f + vf (-bl Sum.inl Sum.inl X) f +
      fou l (mq (-bl Sum.inl Sum.inr X) (fouInv l f)) - ((X.toBlocks₁₁.trace / 2 : ℝ) : ℂ) • f := by sorry
