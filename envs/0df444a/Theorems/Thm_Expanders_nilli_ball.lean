-- Prove2me | Theorems.Thm_Expanders_nilli_ball
-- name    : Expanders.nilli_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:18:47.701255+00:00
-- url     : https://prove2.me/theorems/0113642c-077c-5dbe-a30a-579c32a40b94
-- title:
--   Expanders: nilli ball
-- statement:
--   **Nilli's estimate on a layered ball.** If `B` is layered by `h` (levels `≤ k`, edges change
--   the level by at most one, edges leave `B` only from level `k`, and every vertex of `B` has a
--   neighbour in `B` on a lower level, or on level `0` if it is itself on level `0`), then the test
--   vector `nilliVec (√(d-1)) B h` has Rayleigh quotient at least `2√(d-1) - (2√(d-1)-1)/(k+1)`.
--
--   Source: https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L194-L337
-- source:
--   https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L194-L337

module
public import Mathlib
public import Definitions.Def_ExpanderLib_NilliBall
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open Expanders
variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] {d k : ℕ} (B : Finset V) (h : V → ℕ)

theorem Expanders.nilli_ball (hd2 : 2 ≤ d) (hd : G.IsRegularOfDegree d)
    (hB : ∀ v ∈ B, h v ≤ k)
    (hout : ∀ v ∈ B, ∀ w, G.Adj v w → w ∉ B → h v = k)
    (hstep : ∀ v ∈ B, ∀ w ∈ B, G.Adj v w → h w ≤ h v + 1)
    (hpar : ∀ v ∈ B, ∃ w ∈ B, G.Adj v w ∧ h w ≤ h v - 1) :
    (2 * Real.sqrt (d - 1) - (2 * Real.sqrt (d - 1) - 1) / (k + 1)) *
        dotProduct (nilliVec (Real.sqrt (d - 1)) B h) (nilliVec (Real.sqrt (d - 1)) B h) ≤
      dotProduct (nilliVec (Real.sqrt (d - 1)) B h)
        (G.adjMatrix ℝ *ᵥ nilliVec (Real.sqrt (d - 1)) B h) := by sorry
