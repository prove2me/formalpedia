-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_ckOn_list_sum
-- name    : Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_list_sum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:18:17.471268+00:00
-- url     : https://prove2.me/theorems/90718061-7085-461b-b1d0-e04eddf6b0f2
-- title:
--   Minor Polynomials: ck On list sum
-- statement:
--   The Minor Polynomials construction uses the ck On list sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComposeDifferentialOperators.lean#L70-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComposeDifferentialOperators.lean#L70-L78

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListMapSumApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComposeDifferentialOperators
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

theorem Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_list_sum {m : ℕ∞} {α : Type*} (L : List α) (f : α → Mat k r → (Wq →L[ℂ] Wp))
    (h : ∀ a ∈ L, CkOn m (GV k r) (f a)) : CkOn m (GV k r) (fun g => (L.map fun a => f a g).sum) := by sorry
