-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_Hpk_levPos
-- name    : Formalism.FourierDecayAlt.P.B2x4.Hpk_levPos
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:26:07.372959+00:00
-- url     : https://prove2.me/theorems/0646e8e4-bf5d-419e-afd0-9e98cc1148d8
-- title:
--   B2x4: Hpk lev Pos
-- statement:
--   The B2x4 construction uses the Hpk lev Pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConjugationInvarianceEverySetting.lean#L137-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConjugationInvarianceEverySetting.lean#L137-L146

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem Formalism.FourierDecayAlt.P.B2x4.Hpk_levPos (k r' : ℕ) (i j : Fin (2 * r' + k + 1)) :
    Hpk k (1 + r') (levPos k 1 r' i) (levPos k 1 r' j) = Hpk k r' i j := by sorry
