-- Prove2me | Theorems.Thm_CompanionTheory_ThKF_E_eq_of_inner
-- name    : CompanionTheory.ThKF.E.eq_of_inner
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:52.548164+00:00
-- url     : https://prove2.me/theorems/bc79c07b-d573-4593-b4df-1a8bec7fa9c7
-- title:
--   E: eq of inner
-- statement:
--   The E construction uses the eq of inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/InnerProductFactorization/EqOfInner.lean#L102-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/InnerProductFactorization/EqOfInner.lean#L102-L107

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

theorem CompanionTheory.ThKF.E.eq_of_inner {u v : Sch l} (h : ∀ φ : Sch l, inner ℂ (φ.toLp 2 volume) (u.toLp 2 volume) =
    inner ℂ (φ.toLp 2 volume) (v.toLp 2 volume)) : u = v := by sorry
