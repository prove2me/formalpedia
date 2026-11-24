-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_mem_steps_of_mem
-- name    : Formalism.FourierDecayAlt.P.MinorPolynomials.mem_steps_of_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:19:55.392799+00:00
-- url     : https://prove2.me/theorems/d779c5a9-ae9a-4a60-bd66-5e42594e874b
-- title:
--   Minor Polynomials: mem steps of mem
-- statement:
--   The Minor Polynomials construction uses the mem steps of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComposeDifferentialOperators.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComposeDifferentialOperators.lean#L17-L24

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

theorem Formalism.FourierDecayAlt.P.MinorPolynomials.mem_steps_of_mem (D : RealPlaceData k r Wp Wq) {nf : ℕ} {e : CT k r nf × List (Mat k r)} {Lf : FS k r nf}
    (he : e ∈ Lf) : ∀ w : List (Mat k r), (e.1, w ++ e.2) ∈ steps D w Lf := by sorry
