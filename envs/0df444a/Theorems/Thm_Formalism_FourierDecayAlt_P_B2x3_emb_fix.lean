-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_fix
-- name    : Formalism.FourierDecayAlt.P.B2x3.emb_fix
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:54:58.482785+00:00
-- url     : https://prove2.me/theorems/7efdf800-88fc-492a-a8e8-f455674247c2
-- title:
--   B2x3: emb fix
-- statement:
--   The B2x3 construction uses the emb fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean#L583-L586
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OppositeWeylSubgroupClosed.lean#L583-L586

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.B2x3.emb_fix (a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i : Fin (2 * r + k + 1)) (hi : ¬ mid k r i) :
    embWb k r a *ᵥ bvec i = bvec i := by sorry
