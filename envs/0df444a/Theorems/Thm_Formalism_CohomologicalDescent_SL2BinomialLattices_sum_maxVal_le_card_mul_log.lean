-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_sum_maxVal_le_card_mul_log
-- name    : Formalism.CohomologicalDescent.SL2BinomialLattices.sum_maxVal_le_card_mul_log
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:00:57.94608+00:00
-- url     : https://prove2.me/theorems/e51103a2-9acc-4f57-a502-ea26c162a26e
-- title:
--   SL2 Binomial Lattices: sum max Val le card mul log
-- statement:
--   The SL2 Binomial Lattices construction uses the sum max Val le card mul log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SL2BinomialLattices.lean#L41-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SL2BinomialLattices.lean#L41-L56

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

theorem Formalism.CohomologicalDescent.SL2BinomialLattices.sum_maxVal_le_card_mul_log {N : ℕ} (U : Fin N → ℤ) (l M : ℕ) (hl : 0 < l) (s : Finset (Fin N × Fin N))
    (h : ∀ p ∈ s, U p.1 - U p.2 ≤ (M : ℤ)) :
    ∑ p ∈ s, Formalism.RankGapBounds.JumpSetsAlt.maxVal l (U p.1 - U p.2 - 1).toNat ≤ s.card * Nat.log l M ∧
      (M ≤ l → ∑ p ∈ s, Formalism.RankGapBounds.JumpSetsAlt.maxVal l (U p.1 - U p.2 - 1).toNat = 0) := by sorry
