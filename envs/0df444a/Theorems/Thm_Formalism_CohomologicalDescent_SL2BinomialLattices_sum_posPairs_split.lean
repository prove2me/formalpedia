-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_sum_posPairs_split
-- name    : Formalism.CohomologicalDescent.SL2BinomialLattices.sum_posPairs_split
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:59:49.596933+00:00
-- url     : https://prove2.me/theorems/0ab12663-b4cf-439a-a5df-5f6e224c9e2f
-- title:
--   SL2 Binomial Lattices: sum pos Pairs split
-- statement:
--   The SL2 Binomial Lattices construction uses the sum pos Pairs split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SL2BinomialLattices.lean#L91-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SL2BinomialLattices.lean#L91-L104

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

theorem Formalism.CohomologicalDescent.SL2BinomialLattices.sum_posPairs_split {N : ℕ} (k : ℕ) (g : Fin N × Fin N → ℕ) :
    ∑ p ∈ posPairs N, g p = ∑ p ∈ (posPairs N).filter (fun p => p.2.val < k), g p +
      ∑ p ∈ (posPairs N).filter (fun p => k ≤ p.1.val), g p +
      ∑ p ∈ (posPairs N).filter (fun p => p.1.val < k ∧ k ≤ p.2.val), g p := by sorry
