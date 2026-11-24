-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_ibp_identity
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.ibp_identity
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:26.966361+00:00
-- url     : https://prove2.me/theorems/216c18ba-a640-41c3-867d-4556f6a39a06
-- title:
--   Wirtinger Integration By Parts: ibp identity
-- statement:
--   The Wirtinger Integration By Parts construction uses the ibp identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L770-L831
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L770-L831

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

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.ibp_identity {β t : ℂ} (hβ : β ≠ 0) (ht : t ≠ 0) {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → ℂ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) (hne : ∀ x ∈ Ω, fderiv ℂ g x ≠ 0)
    {a : (Fin d → ℂ) → V} (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a) (hsupp : tsupport a ⊆ Ω) :
    ∫ x : Fin d → ℂ, psi β (g x / t) • a x ∂(muPi β (Fin d)) =
      ∑ k : Fin d, (-(2 * t / (Complex.I * β))) •
        ∫ x : Fin d → ℂ, psi β (g x / t) • wirt k (fun y => bk g k y • a y) x ∂(muPi β (Fin d)) := by sorry
