-- Prove2me | Theorems.Thm_CartierDual_exists_coalgHom_addMonoidAlgebra_eq_sum_single_of_isIdempotentElem
-- name    : CartierDual.exists_coalgHom_addMonoidAlgebra_eq_sum_single_of_isIdempotentElem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/01297f2f-4be0-5206-a5ee-a909d5117f58
-- title:
--   Orthogonal idempotents in the Cartier dual give a coalgebra map
-- statement:
--   Let $S$ be a commutative ring and $B$ a commutative $S$-bialgebra which is finite and free as an $S$-module. Write [`CartierDual S B`](def/HopfAlgebra_CartierDual.html#L12) for the $S$-module dual $\operatorname{Hom}_S(B,S)$ equipped with the convolution ring structure dual to the comultiplication of $B$, so that $(\varphi\psi)(b)=\sum_i \varphi(b_i')\psi(b_i'')$ for any representation of $\Delta b$ and the unit element is the counit of $B$. Let $M$ be a finite type with decidable equality and let $e : M \to$ [`CartierDual S B`](def/HopfAlgebra_CartierDual.html#L12) be a family of elements of this ring such that each $e_m$ is idempotent, $e_ae_b=0$ whenever $a\neq b$, and $\sum_{m\in M} e_m = 1$. The assertion is that there exists a morphism of $S$-coalgebras $f : B \to S[M]$, where $S[M]$ is the additive monoid algebra `AddMonoidAlgebra S M` with its standard coalgebra structure in which each basis element is group-like, such that for every $b \in B$ one has $f(b) = \sum_{m\in M} e_m(b)\,[m]$, the sum of the single-support elements `AddMonoidAlgebra.single m (e m b)`.
--
--   This is one direction of the correspondence between coalgebra morphisms $B \to S[M]$ and complete families of pairwise orthogonal idempotents in the dual algebra $B^\vee$; geometrically, such a family is a decomposition of the finite flat scheme attached to $B^\vee$ into clopen pieces indexed by $M$. It is used in the construction of a lift of a coalgebra map to the residue field over a Henselian local ring, via [`CoalgHom.exists_addMonoidAlgebra_lift_residueField_of_henselianLocalRing`](thm.html#CoalgHom.exists_addMonoidAlgebra_lift_residueField_of_henselianLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CartierDual_exists_coalgHom_addMonoidAlgebra_eq_sum_single_of_isIdempotentElem.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open IsLocalRing
open scoped TensorProduct

theorem CartierDual.exists_coalgHom_addMonoidAlgebra_eq_sum_single_of_isIdempotentElem
    {S : Type u} [CommRing S] {B : Type v} [CommRing B] [Bialgebra S B] [Module.Finite S B] [Module.Free S B]
    (M : Type w) [Fintype M] [DecidableEq M]
    (e : M → CartierDual S B)
    (hidem : ∀ m, IsIdempotentElem (e m)) (horth : ∀ a b, a ≠ b → e a * e b = 0) (hsum : ∑ m, e m = 1) :
    ∃ f : B →ₗc[S] AddMonoidAlgebra S M, ∀ b : B, f b = ∑ m, AddMonoidAlgebra.single m (e m b) := by sorry
