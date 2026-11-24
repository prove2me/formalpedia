-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_nat_le_mul_log_real
-- name    : Formalism.CohomologicalDescent.SL2BinomialLattices.nat_le_mul_log_real
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:59:26.630415+00:00
-- url     : https://prove2.me/theorems/203dc2b2-6da2-4f99-be2e-665f6865fbec
-- title:
--   SL2 Binomial Lattices: nat le mul log real
-- statement:
--   The SL2 Binomial Lattices construction uses the nat le mul log real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SL2BinomialLattices.lean#L82-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SL2BinomialLattices.lean#L82-L89

import Definitions.Def_Formalism_PieriBlockIdeals_ExponentBoundCounterexample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_CountLeftInvSeqAlternatingWordEven
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MaxValEqZeroOfLt
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial CategoryTheory TensorProduct
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.SL2BinomialLattices
open Formalism.GradedWeylDivisibility Formalism.RankGapBounds.JumpSetsAlt Formalism.CohomologicalDescent.LA
universe u v u' v'

theorem Formalism.CohomologicalDescent.SL2BinomialLattices.nat_le_mul_log_real (ex c l y : ℕ) (h : ex ≤ c * Nat.log l y) :
    (ex : ℝ) * Real.log l ≤ (c : ℝ) * Real.log y := by sorry
