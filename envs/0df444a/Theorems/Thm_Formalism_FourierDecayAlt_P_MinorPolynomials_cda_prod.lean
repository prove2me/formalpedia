-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_cda_prod
-- name    : Formalism.FourierDecayAlt.P.MinorPolynomials.cda_prod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:45:10.816315+00:00
-- url     : https://prove2.me/theorems/a1d86941-4be1-4670-b64c-014e9e660279
-- title:
--   Minor Polynomials: cda prod
-- statement:
--   The Minor Polynomials construction uses the cda prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemStepsFull.lean#L52-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemStepsFull.lean#L52-L58

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

theorem Formalism.FourierDecayAlt.P.MinorPolynomials.cda_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) {f : ι → Mat k r → ℂ} {x : Mat k r}
    (h : ∀ i ∈ s, ContDiffAt ℝ ∞ (f i) x) : ContDiffAt ℝ ∞ (fun g => ∏ i ∈ s, f i g) x := by sorry
