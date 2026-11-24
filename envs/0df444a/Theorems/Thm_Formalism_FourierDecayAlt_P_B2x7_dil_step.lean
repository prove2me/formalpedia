-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_dil_step
-- name    : Formalism.FourierDecayAlt.P.B2x7.dil_step
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:58:09.47197+00:00
-- url     : https://prove2.me/theorems/91a7f149-a71d-46e5-9350-8793c2ebeb19
-- title:
--   B2x7: dil step
-- statement:
--   The B2x7 construction uses the dil step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationScalesHeisenbergMeasure.lean#L360-L378
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationScalesHeisenbergMeasure.lean#L360-L378

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
open B2x7
open Formalism.FourierDecayAlt.P.B2x7
variable {k r' : ℕ}

theorem Formalism.FourierDecayAlt.P.B2x7.dil_step (μ' : Measure (Mt k r')) [SigmaFinite μ'] (t : ℝ) (ht : 0 < t)
    (h' : μ'.map (conjM (aDil k r' t)) = ENNReal.ofReal ((t ^ kap k r')⁻¹) • μ') :
    (((μHeis k r').prod (μ'.map (levM k r'))).map mulM).map (conjM (aDil k (1 + r') t)) =
      ENNReal.ofReal ((t ^ kap k (1 + r'))⁻¹) • ((μHeis k r').prod (μ'.map (levM k r'))).map mulM := by sorry
