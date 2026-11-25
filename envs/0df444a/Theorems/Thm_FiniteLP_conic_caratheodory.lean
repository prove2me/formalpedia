-- Prove2me | Theorems.Thm_FiniteLP_conic_caratheodory
-- name    : FiniteLP.conic_caratheodory
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:27:09.467819+00:00
-- url     : https://prove2.me/theorems/105d4652-3c35-5ba9-9234-63704c4b221b
-- title:
--   Finite LP: conic caratheodory
-- statement:
--   The Finite LP construction uses the conic caratheodory property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/FiniteLPDuality.lean#L100-L166
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/FiniteLPDuality.lean#L100-L166

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators InnerProductSpace
open Finset
open FiniteLP
set_option maxHeartbeats 2000000

theorem FiniteLP.conic_caratheodory {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    (v : κ → EuclideanSpace ℝ ι) (c : κ → ℝ) (hc : ∀ k, 0 ≤ c k) :
    ∃ (d : κ → ℝ) (s : Finset κ), (∀ k, 0 ≤ d k) ∧ (∀ k ∉ s, d k = 0) ∧
      LinearIndepOn ℝ v s ∧ (∑ k ∈ s, d k • v k) = ∑ k, c k • v k := by sorry
