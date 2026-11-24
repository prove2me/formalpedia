-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_ckOn_mul
-- name    : Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:44:29.790856+00:00
-- url     : https://prove2.me/theorems/9b03e694-22bd-4dc2-9c19-366be5bc290f
-- title:
--   Minor Polynomials: ck On mul
-- statement:
--   The Minor Polynomials construction uses the ck On mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemStepsFull.lean#L92-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemStepsFull.lean#L92-L100

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenBigCellSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemStepsFull
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

theorem Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_mul {UU : Set (Mat k r)} {A B : Mat k r → C6.EndH Wp Wq} (hA : CkOn ⊤ UU A) (hB : CkOn ⊤ UU B) :
    CkOn ⊤ UU (fun g => A g * B g) := by sorry
