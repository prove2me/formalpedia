-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HeisenbergLevelMinors_heisLev_col
-- name    : Formalism.FourierDecayAlt.P.HeisenbergLevelMinors.heisLev_col
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:47:25.017141+00:00
-- url     : https://prove2.me/theorems/354a0274-2442-426a-86ed-f8a395fe5d93
-- title:
--   Heisenberg Level Minors: heis Lev col
-- statement:
--   The Heisenberg Level Minors construction uses the heis Lev col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLevelMinors.lean#L499-L508
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLevelMinors.lean#L499-L508

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JDomBoundOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfJqSmoothOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastLevelSliceOfScalar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormBallVolumes
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLevelMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
open Formalism.FourierDecayAlt.P.B2x6
variable {k r' : ℕ}

theorem Formalism.FourierDecayAlt.P.HeisenbergLevelMinors.heisLev_col (x : Formalism.FourierDecayAlt.B2.HPar k r') (g : Mat k r') (j : Fin (2 * r' + k + 1)) :
    (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) (lv k r' j) (iL k r') = x.1 j := by sorry
