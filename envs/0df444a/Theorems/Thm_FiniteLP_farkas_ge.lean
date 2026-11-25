-- Prove2me | Theorems.Thm_FiniteLP_farkas_ge
-- name    : FiniteLP.farkas_ge
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:27:22.859879+00:00
-- url     : https://prove2.me/theorems/bec09829-a011-48fa-8a12-986904b56497
-- title:
--   Finite LP: farkas ge
-- statement:
--   **Finite Farkas lemma (inequality form).**  If the primal system
--   `x ≥ 0, N x ≥ c` is infeasible, then there is a Farkas certificate `y ≥ 0` with
--   `Nᵀ y ≤ 0` and `⟨c, y⟩ > 0`.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/FiniteLPDuality.lean#L195-L257
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/FiniteLPDuality.lean#L195-L257

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators InnerProductSpace
open Finset
open FiniteLP

theorem FiniteLP.farkas_ge {ι κ : Type*} [Fintype ι] [Fintype κ]
    (N : ι → κ → ℝ) (c : ι → ℝ)
    (hinfeas : ¬ ∃ x : κ → ℝ, (∀ j, 0 ≤ x j) ∧ (∀ i, c i ≤ ∑ j, N i j * x j)) :
    ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ j, ∑ i, N i j * y i ≤ 0) ∧ 0 < ∑ i, c i * y i := by sorry
