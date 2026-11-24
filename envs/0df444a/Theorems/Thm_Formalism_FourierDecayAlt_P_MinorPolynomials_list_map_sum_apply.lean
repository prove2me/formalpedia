-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_list_map_sum_apply
-- name    : Formalism.FourierDecayAlt.P.MinorPolynomials.list_map_sum_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:03:18.781613+00:00
-- url     : https://prove2.me/theorems/86a82e07-eab0-4516-9469-2c8793e8d0f6
-- title:
--   Minor Polynomials: list map sum apply
-- statement:
--   The Minor Polynomials construction uses the list map sum apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListMapSumApply.lean#L148-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ListMapSumApply.lean#L148-L151

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListMapSumApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.MinorPolynomials.list_map_sum_apply {α : Type*} (L : List α) (A : C6.EndH Wp Wq) (f : α → (Wq →L[ℂ] Wp)) :
    A (L.map f).sum = (L.map fun a => A (f a)).sum := by sorry
