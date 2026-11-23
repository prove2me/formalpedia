-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_Har2_card_bideg
-- name    : Formalism.CountingSumsFrames.Har2.card_bideg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:33:17.684635+00:00
-- url     : https://prove2.me/theorems/df164993-f88d-4b9c-a5e2-19045e8730cd
-- title:
--   Har2: card bideg
-- statement:
--   The Har2 construction uses the card bideg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L626-L638
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HarmonicDecompositionHolds.lean#L626-L638

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Har2
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}

theorem Formalism.CountingSumsFrames.Har2.card_bideg (k' A B : ℕ) :
    Nat.card {m : XY (k' + 1) →₀ ℕ | xDeg m = A ∧ yDeg m = B} =
      (A + k').choose k' * (B + k').choose k' := by sorry
