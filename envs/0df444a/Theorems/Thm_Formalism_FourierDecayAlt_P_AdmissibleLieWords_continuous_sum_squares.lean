-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_continuous_sum_squares
-- name    : Formalism.FourierDecayAlt.P.AdmissibleLieWords.continuous_sum_squares
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:25:37.152525+00:00
-- url     : https://prove2.me/theorems/91692041-db8a-4026-8565-4222eac52c7a
-- title:
--   Admissible Lie Words: continuous sum squares
-- statement:
--   The Admissible Lie Words construction uses the continuous sum squares property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Sq2UnitOfEqOneOfSq2EqDiv.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Sq2UnitOfEqOneOfSq2EqDiv.lean#L40-L42

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfUnitWords
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Sq2UnitOfEqOneOfSq2EqDiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ComplexConjugate ContDiff Manifold Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.AdmissibleLieWords.continuous_sum_squares (m : ℕ) : Continuous (C6.sq2 (m := m)) := by sorry
