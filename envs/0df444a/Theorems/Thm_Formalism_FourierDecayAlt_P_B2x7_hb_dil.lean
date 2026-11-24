-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_hb_dil
-- name    : Formalism.FourierDecayAlt.P.B2x7.hb_dil
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:58:25.136538+00:00
-- url     : https://prove2.me/theorems/169a35c4-ecf6-4869-bed8-7012f59c3eaf
-- title:
--   B2x7: hb dil
-- statement:
--   The B2x7 construction uses the hb dil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationScalesHeisenbergMeasure.lean#L175-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationScalesHeisenbergMeasure.lean#L175-L182

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open Formalism.FourierDecayAlt.P.B2x7
variable {k r' : ℕ}

theorem Formalism.FourierDecayAlt.P.B2x7.hb_dil (t : ℝ) (ht : t ≠ 0) (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) :
    hb k r' (((t ^ (1 + r') : ℝ) : ℂ) • (aDil k r' t *ᵥ y)) (t ^ (2 * (1 + r')) * s) =
      ((t ^ (1 + r') : ℝ) : ℂ) ^ 2 * hb k r' y s := by sorry
