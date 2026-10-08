-- Prove2me | Theorems.Thm_FiniteMagmaE677_product_e677
-- name    : FiniteMagmaE677.product_e677
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T18:17:43.727+00:00
-- url     : https://prove2.me/theorems/d97072de-a1a4-429d-b6e6-13869b4d808b
-- title:
--   Products of E677 magmas satisfy E677
-- statement:
--   If operations $\diamond_1$ on $A$ and $\diamond_2$ on $B$ both satisfy equation 677, then the componentwise operation on $A \times B$,
--
--   $$(p_1, p_2) \diamond (q_1, q_2) = (p_1 \diamond_1 q_1,\; p_2 \diamond_2 q_2),$$
--
--   also satisfies equation 677: the identity holds coordinatewise.
-- source:
--   Standard closure property of equational classes, specialized to E677; recorded for the Prove2Me mission 'Equational Magmas: E677 → E255 (finite case)'.

import Definitions.Def_FiniteMagmaE677

universe u v

theorem FiniteMagmaE677.product_e677 {α : Type u} {β : Type v}
    (op₁ : α → α → α) (op₂ : β → β → β)
    (h₁ : FiniteMagmaE677.E677 op₁) (h₂ : FiniteMagmaE677.E677 op₂) :
    FiniteMagmaE677.E677 (fun p q : α × β => (op₁ p.1 q.1, op₂ p.2 q.2)) := by sorry
