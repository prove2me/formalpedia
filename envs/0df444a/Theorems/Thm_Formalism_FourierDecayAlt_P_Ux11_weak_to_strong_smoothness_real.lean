-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_weak_to_strong_smoothness_real
-- name    : Formalism.FourierDecayAlt.P.Ux11.weak_to_strong_smoothness_real
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:24:40.522799+00:00
-- url     : https://prove2.me/theorems/3dd64053-a4d7-4361-b391-ece00683c5f2
-- title:
--   Ux11: weak to strong smoothness real
-- statement:
--   The Ux11 construction uses the weak to strong smoothness real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakToStrongSmoothnessReal.lean#L178-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakToStrongSmoothnessReal.lean#L178-L275

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

theorem Formalism.FourierDecayAlt.P.Ux11.weak_to_strong_smoothness_real (m : ℕ) : ∀ (V I : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (lam : I → V →L[ℝ] E), Norming lam → ∀ (Ω : Set X) (Φ : X → V) (bd : X → ℝ), IsOpen Ω →
    ContinuousOn bd Ω →
    (∀ i, ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun x => lam i (Φ x)) Ω) →
    (∀ i, ∀ q ≤ m + 1, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ q (fun x => lam i (Φ x)) x‖ ≤ bd x) →
    ContDiffOn ℝ (m : WithTop ℕ∞) Φ Ω ∧ ∀ q ≤ m, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ q Φ x‖ ≤ bd x := by sorry
