-- Prove2me | Theorems.Thm_FiniteMagmaE677_product_e255
-- name    : FiniteMagmaE677.product_e255
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T18:17:49.79181+00:00
-- url     : https://prove2.me/theorems/040c1aae-e939-4961-a0c4-805bb4d06211
-- title:
--   Products of E255 magmas satisfy E255
-- statement:
--   If operations $\diamond_1$ on $A$ and $\diamond_2$ on $B$ both satisfy equation 255, then the componentwise operation on $A \times B$ also satisfies equation 255: the identity $x = ((x \diamond x) \diamond x) \diamond x$ holds coordinatewise. Together with the E677 product closure, the class of finite magmas satisfying both equations is closed under products, so product constructions cannot produce finite counterexamples to the implication E677 → E255.
-- source:
--   Standard closure property of equational classes, specialized to E255; recorded for the Prove2Me mission 'Equational Magmas: E677 → E255 (finite case)'.

import Definitions.Def_FiniteMagmaE677

universe u v

theorem FiniteMagmaE677.product_e255 {α : Type u} {β : Type v}
    (op₁ : α → α → α) (op₂ : β → β → β)
    (h₁ : FiniteMagmaE677.E255 op₁) (h₂ : FiniteMagmaE677.E255 op₂) :
    FiniteMagmaE677.E255 (fun p q : α × β => (op₁ p.1 q.1, op₂ p.2 q.2)) := by sorry
