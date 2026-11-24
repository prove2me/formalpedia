-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_skip_two_succAbove_comp_alt
-- name    : Formalism.FourierDecayAlt.P.Qx6.skip_two_succAbove_comp_alt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:34:21.594844+00:00
-- url     : https://prove2.me/theorems/98eab83e-ec9e-4200-b282-f9147cb3ba10
-- title:
--   Qx6: skip two succ Above comp alt
-- statement:
--   The Qx6 construction uses the skip two succ Above comp alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L134-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L134-L153

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

theorem Formalism.FourierDecayAlt.P.Qx6.skip_two_succAbove_comp_alt {t : ℕ} (b : Fin (t + 2)) (a : Fin (t + 1)) :
    (skip2 (min (b.succAbove a) b) (max (b.succAbove a) b) : Fin t → Fin (t + 2)) =
      b.succAbove ∘ a.succAbove := by sorry
