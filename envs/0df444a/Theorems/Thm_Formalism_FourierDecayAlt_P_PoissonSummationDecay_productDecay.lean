-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PoissonSummationDecay_productDecay
-- name    : Formalism.FourierDecayAlt.P.PoissonSummationDecay.productDecay
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:01:49.507107+00:00
-- url     : https://prove2.me/theorems/3e00234d-566e-40c4-a8dd-0c355934addd
-- title:
--   Poisson Summation Decay: product Decay
-- statement:
--   The Poisson Summation Decay construction uses the product Decay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PoissonSummationDecay.lean#L261-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PoissonSummationDecay.lean#L261-L265

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonSummationDecay
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PoissonSummationDecay
open Formalism.FourierDecayAlt.F7
open Finset Polynomial
open MeasureTheory Formalism.H
open scoped FourierTransform RealInnerProductSpace ENNReal

theorem Formalism.FourierDecayAlt.P.PoissonSummationDecay.productDecay : ProductDecaySummable := by sorry
