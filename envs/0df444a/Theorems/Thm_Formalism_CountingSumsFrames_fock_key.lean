-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_fock_key
-- name    : Formalism.CountingSumsFrames.fock_key
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:27.579573+00:00
-- url     : https://prove2.me/theorems/83bbcedc-2327-42c5-930f-80b4b7a5eba1
-- title:
--   Counting Sums Frames: fock key
-- statement:
--   The Counting Sums Frames construction uses the fock key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FockGaussComparisonHolds.lean#L67-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FockGaussComparisonHolds.lean#L67-L76

import Definitions.Def_Formalism_PolynomialDimension_FrameSum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FockGaussComparisonHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames

theorem Formalism.CountingSumsFrames.fock_key {σ Z : Type} [Fintype σ] [Fintype Z] [DecidableEq Z] (letter : σ → Z)
    (d : Z → ℕ) (α : σ →₀ ℕ)
    (h : ∀ z, ∑ i ∈ univ.filter (fun i => letter i = z), α i = d z) :
    ∏ z, (d z).factorial =
      factProd α * ∏ z, Nat.multinomial (univ.filter (fun i => letter i = z)) α := by sorry
