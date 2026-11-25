-- Prove2me | Theorems.Thm_CompanionTheory_ThKF_E_lie
-- name    : CompanionTheory.ThKF.E.lie
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:17:49.671411+00:00
-- url     : https://prove2.me/theorems/e8794469-5dd8-483d-8bdf-aee87590ae99
-- title:
--   E: lie
-- statement:
--   The E construction uses the lie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/InnerProductFactorization/EqOfInner.lean#L238-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/InnerProductFactorization/EqOfInner.lean#L238-L319

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

theorem CompanionTheory.ThKF.E.lie (hP : GlobalTheory.Published.RealMetaplecticRepresentation) (s : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ))
    (sc : ∀ w, Continuous fun t => s t w) (s0 : ∀ w, s 0 w = w) (sm : ∀ t u w, s (t + u) w = s t (s u w))
    (ss : ∀ t w w', sympl (s t w) (s t w') = sympl w w') (S : ℝ → Sch l →ₗ[ℂ] Sch l) (hS : ∀ t, Impl (s t) (S t))
    (S0 : ∀ f, S 0 f = f) (Sm : ∀ t u f, S (t + u) f = S t (S u f))
    (Sc : ∀ f (lam : Sch l →L[ℂ] ℂ), Continuous fun t => lam (S t f)) :
    ∃ Q ∈ weylAlg l, ∀ f (lam : Sch l →L[ℂ] ℂ), HasDerivAt (fun t => lam (S t f)) (lam (Q f)) 0 := by sorry
