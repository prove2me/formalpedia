-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_posPairs_filter_ge
-- name    : Formalism.CohomologicalDescent.SL2BinomialLattices.posPairs_filter_ge
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:59:01.456501+00:00
-- url     : https://prove2.me/theorems/447ef750-350d-4638-a26a-17eda1cb7270
-- title:
--   SL2 Binomial Lattices: pos Pairs filter ge
-- statement:
--   The SL2 Binomial Lattices construction uses the pos Pairs filter ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SL2BinomialLattices.lean#L131-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SL2BinomialLattices.lean#L131-L158

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

theorem Formalism.CohomologicalDescent.SL2BinomialLattices.posPairs_filter_ge {N k : ℕ} (hk : k ≤ N) :
    (posPairs N).filter (fun p => k ≤ p.1.val) =
      (posPairs (N - k)).map ((embedFinLast N k).prodMap (embedFinLast N k)) := by sorry
