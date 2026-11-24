-- Prove2me | Theorems.Thm_CompanionTheory_ThKF_E_Impl_dRho
-- name    : CompanionTheory.ThKF.E.Impl.dRho
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:36.157739+00:00
-- url     : https://prove2.me/theorems/5cd0a7c4-06eb-4807-8f75-d8e816cb4f1b
-- title:
--   Impl: d Rho
-- statement:
--   The Impl construction uses the d Rho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/InnerProductFactorization/EqOfInner.lean#L109-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/InnerProductFactorization/EqOfInner.lean#L109-L119

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

theorem CompanionTheory.ThKF.E.Impl.dRho {s : (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)} {S : Sch l →ₗ[ℂ] Sch l} (h : Impl s S)
    (hs : Function.Surjective S) (w : l ⊕ l → ℝ) (f : Sch l) : S (dRho w f) = dRho (s w) (S f) := by sorry
