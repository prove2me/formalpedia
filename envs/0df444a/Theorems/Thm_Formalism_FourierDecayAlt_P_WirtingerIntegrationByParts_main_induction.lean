-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_main_induction
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.main_induction
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:18.073405+00:00
-- url     : https://prove2.me/theorems/e9bdf18e-eef8-495d-8def-c5e8828f4761
-- title:
--   Wirtinger Integration By Parts: main induction
-- statement:
--   The Wirtinger Integration By Parts construction uses the main induction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L833-L895
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L833-L895

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] {d : ℕ}

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.main_induction {q : ℕ} {β t : ℂ} (hβ : β ≠ 0) (ht : t ≠ 0) {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → ℂ}
    {η P B : ℝ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) (hη : 0 < η) (hP : 0 < P) (hlow : ∀ x ∈ Ω, η ≤ ‖fderiv ℂ g x‖) (hB : 0 ≤ B)
    (hbk : ∀ x ∈ Ω, ∀ k, Bd (bk g k) Ω x q (B / ‖fderiv ℂ g x‖) P) :
    ∀ n ≤ q, ∀ (S : ℝ) (a : (Fin d → ℂ) → V), ContDiff ℝ n a → HasCompactSupport a → tsupport a ⊆ Ω →
      (∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ S * P ^ j) →
      ‖∫ x : Fin d → ℂ, psi β (g x / t) • a x ∂(muPi β (Fin d))‖ ≤
        (2 / ‖β‖ * d * (2 ^ q * B)) ^ n * S * (‖t‖ * P / η) ^ n * (muPi β (Fin d) (tsupport a)).toReal := by sorry
