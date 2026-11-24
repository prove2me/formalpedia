-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_mn_nonneg
-- name    : Formalism.FourierDecayAlt.P.TBBx1.mn_nonneg
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:56:24.690724+00:00
-- url     : https://prove2.me/theorems/6caf1b39-6370-457f-8701-5cee2c38091e
-- title:
--   TBBx1: mn nonneg
-- statement:
--   The TBBx1 construction uses the mn nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinLeTruncatedExponential.lean#L76-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinLeTruncatedExponential.lean#L76-L80

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinLeTruncatedExponential
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx1
open Finset Filter Topology MeasureTheory Real
open Formalism.FourierDecayAlt.TBB
open scoped ComplexConjugate ENNReal NNReal
noncomputable section

theorem Formalism.FourierDecayAlt.P.TBBx1.mn_nonneg {Λ : ℝ} (hΛ : 0 ≤ Λ) (K : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ mn Λ K x := by sorry
