-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx4_normAt_of_pts
-- name    : Formalism.FourierDecayAlt.P.TBBx4.normAt_of_pts
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:59:24.459482+00:00
-- url     : https://prove2.me/theorems/476e59df-fc93-49d3-8695-f93372cfc0af
-- title:
--   TBBx4: norm At of pts
-- statement:
--   The TBBx4 construction uses the norm At of pts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularityAtPlaceOfSubadditive.lean#L147-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularityAtPlaceOfSubadditive.lean#L147-L215

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

theorem Formalism.FourierDecayAlt.P.TBBx4.normAt_of_pts (p : KB.Pl P Wp Wq) (f Fp Fm : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Ap Am : C.LPt → (Wq →L[ℂ] Wq)) (b : ℝ) (n₀ p₀ : ℕ)
    (hVp : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ →
      p.V Fp γ = ((Gp p γ ^ p₀ : ℝ) : ℂ) • (p.V f γ).comp (Ap γ))
    (hVm : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ →
      p.V Fm γ = ((Gp p γ ^ p₀ : ℝ) : ℂ) • (p.V f γ).comp (Am γ))
    (hlow : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ → ∀ v : Wq,
      ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (Tq p / Gp p γ) ^ n₀ *
        (‖(ContinuousLinearMap.adjoint (Ap γ)) v‖ ^ 2 + ‖(ContinuousLinearMap.adjoint (Am γ)) v‖ ^ 2))
    (hnp : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ → ‖Ap γ‖ ^ 2 ≤ (Gp p γ / Tq p) ^ n₀)
    (hnm : ∀ γ, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ → ‖Am γ‖ ^ 2 ≤ (Gp p γ / Tq p) ^ n₀) :
    NormAt p f Fp Fm b n₀ p₀ := by sorry
