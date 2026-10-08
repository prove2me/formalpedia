-- Prove2me | Theorems.Thm_Conway99Formal_automorphisms_order_eleven_aut_quotient_symmetric
-- name    : Conway99Formal.automorphisms.order_eleven_aut_quotient_symmetric
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T20:05:13.977311+00:00
-- url     : https://prove2.me/theorems/8833ab86-c6e7-45d1-80c6-81bfa222b1a5
-- title:
--   Symmetric nine-cell quotient of an order-eleven graph automorphism
-- statement:
--   Let G be a strongly regular graph with parameters (99,14,1,2), and let σ be an automorphism of G of order exactly 11. There are nine σ-invariant cells of eleven vertices and an integer matrix R whose entry R[i,j] is the number of actual neighbors in cell j of each vertex in cell i. The entries are nonnegative, each row sums to 14, and R is symmetric. Symmetry follows by counting graph edges between equal-size cells in both directions. No finite exclusion of such a matrix is asserted.
-- source:
--   Exact original Lean source blob/d748eb34a67ba6001a71c257085a42b14b156240/formalization/2026-10-03/automorphisms/Automorphisms.lean#L621-L635; source SHA-256 838fc9247838eaecbb269aab76095b5517b7bb31820b590c6a41aaa4ba992a90; official Stage 1/2 oracle SHA-256 9ef03cf3429dc8a0433aec0d9c9aadafc83973379f30e533d396e7360a2fd68d / fc4a356eb4d448fbd5152296979927c7962814502f1fbb0f06cf717a7bcb8787. Conditional graph-owned order-eleven quotient checkpoint, not a full graph exclusion.

import Definitions.Def_Automorphisms
import Mathlib

namespace Conway99Formal.automorphisms
end Conway99Formal.automorphisms

set_option autoImplicit false

/-! Automorphisms and their vertex orbits for one literal graph. -/

open Conway99Formal.automorphisms

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem Conway99Formal.automorphisms.order_eleven_aut_quotient_symmetric
    (h : G.IsSRGWith 99 14 1 2) (σ : Equiv.Perm V)
    (hσ : IsAut G σ) (hord : orderOf σ = 11) :
    ∃ c : V → Fin 9, ∃ R : Matrix (Fin 9) (Fin 9) ℤ,
      (∀ x, c (σ x) = c x) ∧
      (∀ i, (Finset.univ.filter fun x => c x = i).card = 11) ∧
      (∀ x i, (((G.neighborFinset x).filter fun y => c y = i).card : ℤ) = R (c x) i) ∧
      (∀ i j, 0 ≤ R i j) ∧
      (∀ i, ∑ j, R i j = 14) ∧ R.transpose = R := by sorry
