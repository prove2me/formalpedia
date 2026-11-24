-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_min_le_truncated_exponential
-- name    : Formalism.FourierDecayAlt.P.TBBx1.min_le_truncated_exponential
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:56:23.003801+00:00
-- url     : https://prove2.me/theorems/033d4b29-63bb-457f-b41d-8c442b0c553b
-- title:
--   TBBx1: min le truncated exponential
-- statement:
--   The TBBx1 construction uses the min le truncated exponential property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinLeTruncatedExponential.lean#L82-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinLeTruncatedExponential.lean#L82-L94

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

theorem Formalism.FourierDecayAlt.P.TBBx1.min_le_truncated_exponential {Λ x : ℝ} (hΛ : 0 ≤ Λ) (hΛx : Λ ≤ x) {K : ℕ} (hK : 3 ≤ K) {t : ℝ} (ht : 0 ≤ t) :
    mn Λ K t ≤ Formalism.HermitianLatticeCounting.ExpansionTerms.TruncationCutoff 3 x t := by sorry
