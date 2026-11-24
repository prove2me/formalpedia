-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_ubl_fib
-- name    : Formalism.FourierDecayAlt.P.AdmissibleLieWords.ubl_fib
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:41:50.023497+00:00
-- url     : https://prove2.me/theorems/dbc72d15-8b4a-4230-821f-fae38b32303f
-- title:
--   Admissible Lie Words: ubl fib
-- statement:
--   The Admissible Lie Words construction uses the ubl fib property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DminStarPd.lean#L94-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DminStarPd.lean#L94-L153

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZinvBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_WeightBoundMultiplicative
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DminStarPd
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

theorem Formalism.FourierDecayAlt.P.AdmissibleLieWords.ubl_fib (D : RealPlaceData k r Wp Wq) (E : Mat k r → C6.EndH Wp Wq) (hE : C6.FibBound D E) {ε : ℝ} (hε : 0 < ε)
    {S : Set (Mat k r)} (hS : ∀ g ∈ S, g ∈ GV k r ∧ ε ≤ Gf k r D.z D.z' g) (v : List (Mat k r))
    (hv : ∀ X ∈ v, inLie k r X) (n : ℕ) :
    UBL (Rw v E) S n (3 * (r + 1) * v.length) (3 * (r + 1)) := by sorry
