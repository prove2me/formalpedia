-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_word_low
-- name    : Formalism.InvariantFactorPaths.L4.word_low
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:38.130859+00:00
-- url     : https://prove2.me/theorems/9f4ac7b9-7eed-4931-8f82-bb78567b56f0
-- title:
--   L4: word low
-- statement:
--   The L4 construction uses the word low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L78-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersHolds.lean#L78-L101

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM.M MvPolynomial Finset Formalism.CountingSumsFrames
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}

theorem Formalism.InvariantFactorPaths.L4.word_low [NeZero r] (LL : Letters N) (j : ℕ) (M : WithTop ℤ) (l : List (Fin r)) :
    ∀ a b : Fin r, a ≠ 0 → ∀ G : MvPolynomial (Fin N × Fin r) ℚ_[p],
      (∀ l', wd p LL j l' G ∈ SuppLE p LL j M) → wd p LL j l (glAct p LL j a b G) ∈ SuppLE p LL j M := by sorry
