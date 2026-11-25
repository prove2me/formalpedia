-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx4_V_zero
-- name    : Formalism.FourierDecayAlt.P.TBBx4.V_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:54:40.392784+00:00
-- url     : https://prove2.me/theorems/df649f15-e471-50c6-8021-94a7c278e849
-- title:
--   TBBx4: V zero
-- statement:
--   The TBBx4 construction uses the V zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularityAtPlaceOfSubadditive.lean#L72-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RegularityAtPlaceOfSubadditive.lean#L72-L75

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

theorem Formalism.FourierDecayAlt.P.TBBx4.V_zero (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) {γ : C.LPt}
    (hγ : ¬ (D.IsLocPt γ (P.r + 1) ∧ 0 < Gp p γ)) : p.V F γ = 0 := by sorry
