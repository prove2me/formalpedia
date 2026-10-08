-- Prove2me | Theorems.Thm_FiniteMagmaE677_linear_extension_e255
-- name    : FiniteMagmaE677.linear_extension_e255
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T06:39:47.76419+00:00
-- url     : https://prove2.me/theorems/8916bf81-c046-4f59-b99f-2754e007c351
-- title:
--   No counterexamples via linear extension: fibered products over a 255-satisfying base satisfy 255
-- statement:
--   Let $G$ be a finite magma satisfying E677 and E255, $M$ a finite abelian group, and let
--
--   $$(x, s) \diamond (y, t) = (x \diamond_G y,\; \alpha_{x,y} s + \beta_{x,y} t + c_{x,y})$$
--
--   with additive endomorphisms $\alpha_{x,y}, \beta_{x,y}$ of $M$ and constants $c_{x,y} \in M$. If this operation satisfies E677, it also satisfies E255: linear extensions of a 255-satisfying base by an abelian group with endomorphism fibers never produce finite counterexamples to the implication E677 → E255. This is the blueprint Chapter 13 "no counterexamples via linear extension" lemma.
--
--   The proof shows the fiber map $\alpha_{x,y}$ is injective whenever $x$ fixes $y$: if $\alpha_{x,y} s = \alpha_{x,y} s'$, the left translations $L_{(x,s)}$ and $L_{(x,s')}$ agree on the $y$-fiber, the base identity $y \diamond (y \diamond x) = y$ places the middle composite of the two E677 identities in that fiber, and cancelling three injective left translations yields $s = s'$. Bijectivity of $\alpha_{x,y}$ then solves the fixer equation for $(y,t)$, and fixer uniqueness converts the fixer into E255.
-- source:
--   Equational Theories Project, online proof blueprint, Chapter 13 (677), 'no counterexamples via linear extension', https://teorth.github.io/equational_theories/blueprint/677-chapter.html; Lean proof contributed here.

import Mathlib.Data.Fintype.Card
import Definitions.Def_FiniteMagmaE677
import Definitions.Def_LinearExtension_opP
import Theorems.Thm_FiniteMagmaE677_left_bijective
import Theorems.Thm_FiniteMagmaE677_fixer_unique

universe u v

theorem FiniteMagmaE677.linear_extension_e255 {G : Type u} [Fintype G] (opG : G → G → G)
    (hG : FiniteMagmaE677.E677 opG) (hG255 : FiniteMagmaE677.E255 opG)
    {M : Type v} [AddCommGroup M] [Fintype M]
    (α β : G → G → (M →+ M)) (c : G → G → M)
    (h : FiniteMagmaE677.E677 (LinearExtension.opP opG α β c)) :
    FiniteMagmaE677.E255 (LinearExtension.opP opG α β c) := by sorry
