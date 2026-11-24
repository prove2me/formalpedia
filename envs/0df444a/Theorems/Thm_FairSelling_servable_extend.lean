-- Prove2me | Theorems.Thm_FairSelling_servable_extend
-- name    : FairSelling.servable_extend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:30:35.959808+00:00
-- url     : https://prove2.me/theorems/81096f0c-1ae2-4302-86ba-9dce6c5e38f5
-- title:
--   Fair Selling: servable extend
-- statement:
--   Serving one agent `j` a bundle `B` of goods plus `a` units of money (raised from the banked
--   cash and from force-selling the goods `F₀`), and then serving the remaining agents out of what is
--   left.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSApprox.lean#L95-L172
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSApprox.lean#L95-L172

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSApprox
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]

theorem FairSelling.servable_extend (v : Fin n → G → ℝ) (p : G → ℝ) (τ : Fin n → ℝ)
    {T : Finset (Fin n)} {R : Finset G} {D : ℝ}
    (j : Fin n) (hj : j ∈ T) (B F₀ : Finset G) (a : ℝ)
    (hB : B ⊆ R) (hF₀ : F₀ ⊆ R) (hBF : Disjoint B F₀)
    (ha : 0 ≤ a) (hserve : τ j ≤ vbarSum (v j) p B + a)
    (hrec : Servable v p τ (T.erase j) (R \ (B ∪ F₀)) (D + (∑ g ∈ F₀, p g) - a)) :
    Servable v p τ T R D := by sorry
