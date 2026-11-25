-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxI_ckOn_sub
-- name    : Formalism.FourierDecayAlt.P.JFxI.ckOn_sub
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:36:46.128493+00:00
-- url     : https://prove2.me/theorems/94afca9c-b8b4-5fc1-b57c-60d4427d5b6b
-- title:
--   JFx I: ck On sub
-- statement:
--   The JFx I construction uses the ck On sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfExhaustOfAvgCutoff.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfExhaustOfAvgCutoff.lean#L47-L49

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfBetaAdjCOfLemmaBNorm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDiagonalMap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellInversePair
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordIntegralScaling
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothWordsAll
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliUnderIntegral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfExhaustOfAvgCutoff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxI
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.JFxI.ckOn_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {U V : Set (Mat k r)}
    (hUV : U ⊆ V) {f : Mat k r → E} (h : CkOn m V f) : CkOn m U f := by sorry
