-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_hasFDeriv_of
-- name    : Formalism.FourierDecayAlt.P.Ux11.hasFDeriv_of
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:24:46.818803+00:00
-- url     : https://prove2.me/theorems/4b442da0-f2bc-403d-8e22-ac357a2db01c
-- title:
--   Ux11: has FDeriv of
-- statement:
--   The Ux11 construction uses the has FDeriv of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakToStrongSmoothnessReal.lean#L152-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakToStrongSmoothnessReal.lean#L152-L176

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakToStrongSmoothnessReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux11
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ X]

theorem Formalism.FourierDecayAlt.P.Ux11.hasFDeriv_of {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {lam : I → V →L[ℝ] E} (hN : Norming lam) {Φ : X → V} {x₀ : X} {r M : ℝ} (hr : 0 < r)
    (D : I → X →L[ℝ] E)
    (hT : ∀ i, ∀ h : X, ‖h‖ < r → ‖lam i (Φ (x₀ + h)) - lam i (Φ x₀) - D i h‖ ≤ M * ‖h‖ ^ 2) :
    ∃ L : X →L[ℝ] V, HasFDerivAt Φ L x₀ ∧ ∀ i, (lam i).comp L = D i := by sorry
