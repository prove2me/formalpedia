-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_norm_bound_at_place
-- name    : Formalism.FourierDecayAlt.P.norm_bound_at_place
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:37:20.63652+00:00
-- url     : https://prove2.me/theorems/189c6709-f4f3-4cad-b0ac-e253a8d2c6cf
-- title:
--   P: norm bound at place
-- statement:
--   The P construction uses the norm bound at place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularityAtPlaceOfSubadditive.lean#L364-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularityAtPlaceOfSubadditive.lean#L364-L377

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularityAtPlaceOfSubadditive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

theorem Formalism.FourierDecayAlt.P.norm_bound_at_place {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap Am : B.Mat P.k P.r → (Wq →L[ℂ] Wq))
    (ApPt AmPt : C.LPt → (Wq →L[ℂ] Wq)) (b : ℝ) (n₀ p₀ : ℕ)
    (hAp : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
      p.V (fun g => (f g).comp (Ap g)) γ = (p.V f γ).comp (ApPt γ))
    (hAm : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
      p.V (fun g => (f g).comp (Am g)) γ = (p.V f γ).comp (AmPt γ))
    (hlow : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ → ∀ v : Wq,
      ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (TBB.Tq p / TBB.Gp p γ) ^ n₀ *
        (‖(ContinuousLinearMap.adjoint (ApPt γ)) v‖ ^ 2 + ‖(ContinuousLinearMap.adjoint (AmPt γ)) v‖ ^ 2))
    (hnp : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ → ‖ApPt γ‖ ^ 2 ≤ (TBB.Gp p γ / TBB.Tq p) ^ n₀)
    (hnm : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ → ‖AmPt γ‖ ^ 2 ≤ (TBB.Gp p γ / TBB.Tq p) ^ n₀) :
    Formalism.FourierDecayAlt.TBB.NormAt p f (TBBx4.fpm p f Ap p₀) (TBBx4.fpm p f Am p₀) b n₀ p₀ := by sorry
