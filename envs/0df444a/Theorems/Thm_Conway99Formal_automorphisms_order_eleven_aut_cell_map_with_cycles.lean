-- Prove2me | Theorems.Thm_Conway99Formal_automorphisms_order_eleven_aut_cell_map_with_cycles
-- name    : Conway99Formal.automorphisms.order_eleven_aut_cell_map_with_cycles
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T18:32:33.099481+00:00
-- url     : https://prove2.me/theorems/d42ea677-e338-413a-bd31-d39e642bd51d
-- title:
--   Nine eleven-vertex cycles from an order-eleven graph automorphism
-- statement:
--   Let G be a strongly regular graph with parameters (99,14,1,2), and let σ be an automorphism of G with order exactly 11. There is a map c from the vertices of G to nine labels such that c(σ(x))=c(x), every label occurs on exactly eleven vertices, and vertices with the same label lie in the same cycle of σ. The cells come from the actual automorphism of the supplied graph.
-- source:
--   Exact original Lean source blob/d748eb34a67ba6001a71c257085a42b14b156240/formalization/2026-10-03/automorphisms/Automorphisms.lean#L446-L456; source SHA-256 838fc9247838eaecbb269aab76095b5517b7bb31820b590c6a41aaa4ba992a90; official Stage 1/2 oracle SHA-256 9ef03cf3429dc8a0433aec0d9c9aadafc83973379f30e533d396e7360a2fd68d / fc4a356eb4d448fbd5152296979927c7962814502f1fbb0f06cf717a7bcb8787. Conditional graph-owned order-eleven quotient checkpoint, not a full graph exclusion.

import Definitions.Def_Automorphisms
import Mathlib

namespace Conway99Formal.automorphisms
end Conway99Formal.automorphisms

set_option autoImplicit false

/-! Automorphisms and their vertex orbits for one literal graph. -/

open Conway99Formal.automorphisms

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem Conway99Formal.automorphisms.order_eleven_aut_cell_map_with_cycles
    (h : G.IsSRGWith 99 14 1 2) (σ : Equiv.Perm V)
    (hσ : IsAut G σ) (hord : orderOf σ = 11) :
    ∃ c : V → Fin 9,
      (∀ x, c (σ x) = c x) ∧
      (∀ i, (Finset.univ.filter fun x => c x = i).card = 11) ∧
      ∀ x y, c x = c y → σ.SameCycle x y := by sorry
