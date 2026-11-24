-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_key
-- name    : Formalism.FourierDecayAlt.P.B2x9.key
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:43:41.397544+00:00
-- url     : https://prove2.me/theorems/1774be4e-23d7-468d-b4e4-c536e8616bf3
-- title:
--   B2x9: key
-- statement:
--   The B2x9 construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianLeviVectorBaseOrthogonal.lean#L444-L466
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianLeviVectorBaseOrthogonal.lean#L444-L466

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r r' : ℕ}

theorem Formalism.FourierDecayAlt.P.B2x9.key (hG : ClosedG) (HA : HeisAct) (HI : HeisInv) (OM : OneStepMem) (OC : OneStepCoord) (SD : StabDecomp)
    (hP : IsClosedSubgroup (P1set k r')) (a : Mat k (1 + r')) (ha : a ∈ GV k (1 + r')) (p : ℂ × HPar k r') (hc : p.1 ≠ 0)
    (hv : (a *ᵥ xi k r' p) (iL k r') ≠ 0) :
    ∃ q ∈ P1set k r', a * (Matrix.of (tau k r' p) : Mat k (1 + r')) =
      (Matrix.of (tau k r' (eta k r' (a *ᵥ xi k r' p))) : Mat k (1 + r')) * q := by sorry
