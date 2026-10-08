-- Prove2me | Theorems.Thm_Conway99Formal_automorphisms_order_eleven_aut_quotient_counts
-- name    : Conway99Formal.automorphisms.order_eleven_aut_quotient_counts
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T19:15:14.18354+00:00
-- url     : https://prove2.me/theorems/d33ef52d-4b76-4783-9bcf-3d1177183cd5
-- title:
--   Actual nine-cell neighbor-count quotient for an order-eleven automorphism
-- statement:
--   Let G be a strongly regular graph with parameters (99,14,1,2), and let σ be an automorphism of G of order 11. There are nine σ-invariant cells of eleven vertices and an integer 9-by-9 matrix R. For every graph vertex x and cell j, R[c(x),j] equals the number of actual neighbors of x in cell j. Every matrix entry is nonnegative, and every row sums to 14. The theorem asserts these constraints for the same supplied graph and automorphism.
-- source:
--   Exact original Lean source blob/d748eb34a67ba6001a71c257085a42b14b156240/formalization/2026-10-03/automorphisms/Automorphisms.lean#L523-L561; source SHA-256 838fc9247838eaecbb269aab76095b5517b7bb31820b590c6a41aaa4ba992a90; official Stage 1/2 oracle SHA-256 9ef03cf3429dc8a0433aec0d9c9aadafc83973379f30e533d396e7360a2fd68d / fc4a356eb4d448fbd5152296979927c7962814502f1fbb0f06cf717a7bcb8787. Conditional graph-owned order-eleven quotient checkpoint, not a full graph exclusion.

import Definitions.Def_Automorphisms
import Mathlib

namespace Conway99Formal.automorphisms
end Conway99Formal.automorphisms

set_option autoImplicit false

/-! Automorphisms and their vertex orbits for one literal graph. -/

open Conway99Formal.automorphisms

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem Conway99Formal.automorphisms.order_eleven_aut_quotient_counts
    (h : G.IsSRGWith 99 14 1 2) (σ : Equiv.Perm V)
    (hσ : IsAut G σ) (hord : orderOf σ = 11) :
    ∃ c : V → Fin 9, ∃ R : Matrix (Fin 9) (Fin 9) ℤ,
      (∀ x, c (σ x) = c x) ∧
      (∀ i, (Finset.univ.filter fun x => c x = i).card = 11) ∧
      (∀ x i, (((G.neighborFinset x).filter fun y => c y = i).card : ℤ) = R (c x) i) ∧
      (∀ i j, 0 ≤ R i j) ∧
      ∀ i, ∑ j, R i j = 14 := by sorry
