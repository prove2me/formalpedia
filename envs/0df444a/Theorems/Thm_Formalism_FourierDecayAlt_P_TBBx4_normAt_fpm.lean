-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx4_normAt_fpm
-- name    : Formalism.FourierDecayAlt.P.TBBx4.normAt_fpm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:57:57.222737+00:00
-- url     : https://prove2.me/theorems/49fadd64-527c-4a7b-9f3f-f26b28d913b9
-- title:
--   TBBx4: norm At fpm
-- statement:
--   The TBBx4 construction uses the norm At fpm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularityAtPlaceOfSubadditive.lean#L221-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularityAtPlaceOfSubadditive.lean#L221-L236

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx4
open MeasureTheory Filter Topology Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB
open scoped ENNReal ComplexConjugate
noncomputable section
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem Formalism.FourierDecayAlt.P.TBBx4.normAt_fpm (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Ap Am : B.Mat P.k P.r → (Wq →L[ℂ] Wq)) (ApPt AmPt : C.LPt → (Wq →L[ℂ] Wq)) (b : ℝ) (n₀ p₀ : ℕ)
    (hAp : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ →
      p.V (fun g => (f g).comp (Ap g)) γ = (p.V f γ).comp (ApPt γ))
    (hAm : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ →
      p.V (fun g => (f g).comp (Am g)) γ = (p.V f γ).comp (AmPt γ))
    (hlow : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ → ∀ v : Wq,
      ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ *
        (‖(ContinuousLinearMap.adjoint (ApPt γ)) v‖ ^ 2 + ‖(ContinuousLinearMap.adjoint (AmPt γ)) v‖ ^ 2))
    (hnp : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ → ‖ApPt γ‖ ^ 2 ≤ (Gp p γ / Tq p) ^ n₀)
    (hnm : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ → ‖AmPt γ‖ ^ 2 ≤ (Gp p γ / Tq p) ^ n₀) :
    NormAt p f (fpm p f Ap p₀) (fpm p f Am p₀) b n₀ p₀ := by sorry
