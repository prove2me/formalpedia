-- Prove2me | Theorems.Thm_CompanionTheory_ThKF_E_exists_lift
-- name    : CompanionTheory.ThKF.E.exists_lift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:57.581704+00:00
-- url     : https://prove2.me/theorems/d2e921d2-9209-49fe-916e-c72e04e15245
-- title:
--   E: exists lift
-- statement:
--   The E construction uses the exists lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/InnerProductFactorization/EqOfInner.lean#L212-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/InnerProductFactorization/EqOfInner.lean#L212-L236

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_CompanionTheory_ThickeningEstimates_InnerProductFactorization_EqOfInner
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKF CompanionTheory.ThKF.E
variable {l : Type} [Fintype l] [DecidableEq l]

theorem CompanionTheory.ThKF.E.exists_lift (hP : GlobalTheory.Published.RealMetaplecticRepresentation) {X : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) : ∃ (U : ℝ → Sch l →L[ℂ] Sch l) (Q : Sch l →L[ℂ] Sch l), Q ∈ weylAlg l ∧
      (∀ f, U 0 f = f) ∧ (∀ s t f, U (s + t) f = U s (U t f)) ∧
      (∀ t, Impl (fun w => NormedSpace.exp (t • X) *ᵥ w) (U t).toLinearMap) ∧
      (∀ f, Continuous fun t => (U t f).toLp 2 volume) ∧
      ∀ f (lam : Sch l →L[ℂ] ℂ), HasDerivAt (fun t => lam (U t f)) (lam (Q f)) 0 := by sorry
