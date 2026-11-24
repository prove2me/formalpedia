-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bk_bound
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bk_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:55.432353+00:00
-- url     : https://prove2.me/theorems/14132346-1deb-4ae0-99ac-474a211909d8
-- title:
--   Wirtinger Integration By Parts: bk bound
-- statement:
--   The Wirtinger Integration By Parts construction uses the bk bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L606-L655
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L606-L655

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

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bk_bound (d q : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ (Ω : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → ℂ) (P : ℝ), IsOpen Ω →
    DifferentiableOn ℂ g Ω → 0 < P → (∀ x ∈ Ω, fderiv ℂ g x ≠ 0) → ∀ x ∈ Ω,
    (∀ j : ℕ, 1 ≤ j → j ≤ q → ‖iteratedFDeriv ℂ (j + 1) g x‖ ≤ ‖fderiv ℂ g x‖ * P ^ j) →
    ∀ k : Fin d, Bd (bk g k) Ω x q (B / ‖fderiv ℂ g x‖) P := by sorry
