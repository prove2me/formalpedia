-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx4_vec_Gpow
-- name    : Formalism.FourierDecayAlt.P.TBBx4.vec_Gpow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:58:49.586374+00:00
-- url     : https://prove2.me/theorems/647ffdde-e32d-4f3a-a8b5-920bd6cb23d8
-- title:
--   TBBx4: vec Gpow
-- statement:
--   The TBBx4 construction uses the vec Gpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularityAtPlaceOfSubadditive.lean#L122-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularityAtPlaceOfSubadditive.lean#L122-L138

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

theorem Formalism.FourierDecayAlt.P.TBBx4.vec_Gpow (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (p₀ : ℕ) {γ : C.LPt}
    (_hγ : D.IsLocPt γ (P.r + 1)) (hG : 0 < Gp p γ) :
    p.V (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • F g) γ =
      ((Gp p γ ^ p₀ : ℝ) : ℂ) • p.V F γ := by sorry
