-- Prove2me | Theorems.Thm_FiniteMagmaE677_period_four_r_second_step_eight_elements
-- name    : FiniteMagmaE677.period_four_r_second_step_eight_elements
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-26T08:20:23.69561+00:00
-- url     : https://prove2.me/theorems/a6dcf6b8-14e5-4c6f-8357-b93c0ce1e23e
-- title:
--   R second-step branch requires at least eight elements
-- statement:
--   Let a finite magma satisfy E677, and let a D4 distinguished packet give the four pairwise distinct points x, c₁, c₂, c₃ with Lₓ(x)=c₁, Lₓ(c₁)=c₂, Lₓ(c₂)=c₃, Lₓ(c₃)=x. Set q=c₂⋄x and r=c₁⋄c₂. Retain the packet identities q=c₃⋄x, c₁⋄q=x, c₂⋄q=c₁ and q outside the four points. Assume the tagged R start (in particular, r is outside those five points) and Lₓ(q)=r.
--
--   Then the finite carrier has at least eight elements.
--
--   This strengthens the seven-element requirement for the R second-step branch. The proof constructs eight distinct elements by algebraic case analysis, using the established lower bound of six for the seed's own L_q orbit. It does not enumerate finite multiplication tables. It excludes this branch on carriers of size at most seven; it does not close D4.3b on arbitrary finite carriers.
-- source:
--   Original auxiliary deduction for D4.3b (https://prove2.me/theorems/98f7dc30-3fa6-4160-89d8-62bd30c5e338), 2026-10-26. Builds on the seed structure proved at https://prove2.me/theorems/980cfd5e-ee3b-40c9-83e0-b7298775881f and the published D4 distinguished and tagged R definitions. The distinct-element construction and residual contact argument are given in the accompanying proof.

import Definitions.Def_FiniteMagmaE677_d4_first_return
import Mathlib.Data.Fintype.Card

universe u

theorem FiniteMagmaE677.period_four_r_second_step_eight_elements {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (x c1 c2 c3 : α)
    (packet : FiniteMagmaE677.FirstReturn.D4Distinguished op x c1 c2 c3)
    (start : FiniteMagmaE677.FirstReturn.RTaggedStart op x c1 c2 c3)
    (q_to_r : op x (op c2 x) = op c1 c2) :
    8 ≤ Fintype.card α := by sorry
