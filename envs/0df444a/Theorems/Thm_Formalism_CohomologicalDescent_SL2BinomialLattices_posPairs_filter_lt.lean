-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_posPairs_filter_lt
-- name    : Formalism.CohomologicalDescent.SL2BinomialLattices.posPairs_filter_lt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:58:28.70791+00:00
-- url     : https://prove2.me/theorems/2a2e3852-d34d-41aa-8411-c94296a12992
-- title:
--   SL2 Binomial Lattices: pos Pairs filter lt
-- statement:
--   The SL2 Binomial Lattices construction uses the pos Pairs filter lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SL2BinomialLattices.lean#L118-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SL2BinomialLattices.lean#L118-L129

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

theorem Formalism.CohomologicalDescent.SL2BinomialLattices.posPairs_filter_lt {N k : ℕ} (hk : k ≤ N) :
    (posPairs N).filter (fun p => p.2.val < k) =
      (posPairs k).map ((embedFinFirst hk).prodMap (embedFinFirst hk)) := by sorry
