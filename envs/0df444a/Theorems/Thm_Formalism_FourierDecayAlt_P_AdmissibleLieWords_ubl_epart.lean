-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_ubl_epart
-- name    : Formalism.FourierDecayAlt.P.AdmissibleLieWords.ubl_epart
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:57:53.590037+00:00
-- url     : https://prove2.me/theorems/b29156ee-c3e4-4749-86fe-f9f3c31e0345
-- title:
--   Admissible Lie Words: ubl epart
-- statement:
--   The Admissible Lie Words construction uses the ubl epart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutoffIteratedFDerivBounded.lean#L28-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutoffIteratedFDerivBounded.lean#L28-L57

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DminStarPd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutoffIteratedFDerivBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.AdmissibleLieWords.ubl_epart (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq)
    (hfib : ∀ j, C6.FibBound D (fib j)) {ε : ℝ} (hε : 0 < ε) {S : Set (Mat k r)}
    (hS : ∀ g ∈ S, g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g) (n : ℕ) :
    ∀ es : List (Fin nf × List (Mat k r)), (∀ e ∈ es, ∀ X ∈ e.2, inLie k r X) →
      UBL (C6.Epart fib es) S n (3 * (r + 1) * (es.map fun e => e.2.length).sum) (3 * (r + 1)) := by sorry
