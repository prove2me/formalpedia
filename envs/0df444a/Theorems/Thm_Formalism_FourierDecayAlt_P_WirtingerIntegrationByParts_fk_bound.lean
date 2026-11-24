-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_fk_bound
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.fk_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:03.930204+00:00
-- url     : https://prove2.me/theorems/299d88eb-f2f3-44e1-aac9-dea588a3aa4f
-- title:
--   Wirtinger Integration By Parts: fk bound
-- statement:
--   The Wirtinger Integration By Parts construction uses the fk bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L734-L768
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L734-L768

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

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.fk_bound {q n : ℕ} (hn : n ≤ q) {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → ℂ} {η P B S : ℝ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) (hη : 0 < η) (hP : 0 < P) (hlow : ∀ x ∈ Ω, η ≤ ‖fderiv ℂ g x‖) (hB : 0 ≤ B)
    (hbk : ∀ x ∈ Ω, ∀ k, Bd (bk g k) Ω x q (B / ‖fderiv ℂ g x‖) P)
    {a : (Fin d → ℂ) → V} (ha : ContDiff ℝ n a) (hsupp : tsupport a ⊆ Ω)
    (hb : ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ S * P ^ j) (k : Fin d) :
    ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (fun y => bk g k y • a y) x‖ ≤ (2 ^ q * B * S / η) * P ^ j := by sorry
