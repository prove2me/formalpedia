-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_fock_core
-- name    : Formalism.CountingSumsFrames.fock_core
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:34.245123+00:00
-- url     : https://prove2.me/theorems/1f5afe55-9977-4a40-958b-3add58f1836f
-- title:
--   Counting Sums Frames: fock core
-- statement:
--   The Counting Sums Frames construction uses the fock core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FockGaussComparisonHolds.lean#L78-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/FockGaussComparisonHolds.lean#L78-L125

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

theorem Formalism.CountingSumsFrames.fock_core (p : ℕ) [Fact p.Prime] {σ Z : Type} [Fintype σ] [Fintype Z] [DecidableEq Z]
    (letter : σ → Z) (d : Z → ℕ) (N k : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hcard : Fintype.card σ ≤ N * k) (hd : ∀ z, (d z : ℝ) ≤ 2 * a) (α : σ →₀ ℕ)
    (hh : ∀ z, ∑ i ∈ univ.filter (fun i => letter i = z), α i = d z) :
    padicValNat p (factProd α) ≤ padicValNat p (∏ z, (d z).factorial) ∧
      (padicValNat p (∏ z, (d z).factorial) : ℝ) - N * k * (Real.logb p (2 * a + k) + 1) ≤
        padicValNat p (factProd α) := by sorry
