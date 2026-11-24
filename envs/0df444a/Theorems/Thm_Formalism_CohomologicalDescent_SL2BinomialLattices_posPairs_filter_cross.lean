-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_posPairs_filter_cross
-- name    : Formalism.CohomologicalDescent.SL2BinomialLattices.posPairs_filter_cross
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:59:49.28649+00:00
-- url     : https://prove2.me/theorems/fa830494-c063-4674-b3e5-20b35efa656e
-- title:
--   SL2 Binomial Lattices: pos Pairs filter cross
-- statement:
--   The SL2 Binomial Lattices construction uses the pos Pairs filter cross property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SL2BinomialLattices.lean#L160-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SL2BinomialLattices.lean#L160-L181

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

theorem Formalism.CohomologicalDescent.SL2BinomialLattices.posPairs_filter_cross {N k : ℕ} (hk : k ≤ N) :
    (posPairs N).filter (fun p => p.1.val < k ∧ k ≤ p.2.val) =
      ((Finset.univ : Finset (Fin k)).map (embedFinFirst hk)) ×ˢ
        ((Finset.univ : Finset (Fin (N - k))).map (embedFinLast N k)) := by sorry
