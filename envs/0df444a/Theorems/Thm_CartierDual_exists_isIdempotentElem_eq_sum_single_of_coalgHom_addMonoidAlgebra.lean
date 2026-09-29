-- Prove2me | Theorems.Thm_CartierDual_exists_isIdempotentElem_eq_sum_single_of_coalgHom_addMonoidAlgebra
-- name    : CartierDual.exists_isIdempotentElem_eq_sum_single_of_coalgHom_addMonoidAlgebra
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/50efc052-e349-5ede-88c4-c7075f3c35da
-- title:
--   Coalgebra maps B → S[M] give orthogonal idempotents in the Cartier dual
-- statement:
--   Let $S$ be a commutative ring and $B$ a commutative ring carrying a bialgebra structure over $S$ which is finite and free as an $S$-module, and let $M$ be a finite type. The Cartier dual [`CartierDual S B`](def/HopfAlgebra_CartierDual.html#L12) is by definition the $S$-linear dual $\operatorname{Hom}_S(B,S)$, equipped with the ring structure in which multiplication is convolution (the product of $\varphi$ and $\psi$ is $b \mapsto (\varphi \otimes \psi)(\Delta b)$) and the unit is the counit of $B$. Given an $S$-coalgebra homomorphism $f \colon B \to S[M]$ into the additive monoid algebra of $M$ over $S$ (with its natural coalgebra structure, $\Delta[m] = [m] \otimes [m]$, $\varepsilon[m] = 1$), the assertion is that there exists a family $e \colon M \to \operatorname{Hom}_S(B,S)$ of elements of the Cartier dual such that each $e(m)$ is idempotent for the convolution product, $e(a)\,e(b) = 0$ whenever $a \neq b$, $\sum_{m \in M} e(m) = 1$, and for every $b \in B$ one has $f(b) = \sum_{m \in M} \mathrm{single}\,m\,(e(m)(b))$, i.e. the $m$-th coefficient of $f(b)$ is $e(m)(b)$.
--
--   This is one half of the standard dictionary, under Cartier duality for finite flat commutative group schemes, between coalgebra maps $B \to S[M]$ and complete families of orthogonal idempotents in the dual algebra $B^{\vee}$; the converse direction produces a coalgebra map from such a family. It is used in the study of coalgebra maps into monoid algebras over local rings, notably by [`CoalgHom.addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq`](thm.html#CoalgHom.addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq) and [`CoalgHom.exists_addMonoidAlgebra_lift_residueField_of_henselianLocalRing`](thm.html#CoalgHom.exists_addMonoidAlgebra_lift_residueField_of_henselianLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CartierDual_exists_isIdempotentElem_eq_sum_single_of_coalgHom_addMonoidAlgebra.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open IsLocalRing
open scoped TensorProduct

theorem CartierDual.exists_isIdempotentElem_eq_sum_single_of_coalgHom_addMonoidAlgebra
    {S : Type u} [CommRing S] {B : Type v} [CommRing B] [Bialgebra S B] [Module.Finite S B] [Module.Free S B]
    (M : Type w) [Fintype M] [DecidableEq M]
    (f : B →ₗc[S] AddMonoidAlgebra S M) :
    ∃ e : M → CartierDual S B,
      (∀ m, IsIdempotentElem (e m)) ∧ (∀ a b, a ≠ b → e a * e b = 0) ∧ ∑ m, e m = 1 ∧
      ∀ b : B, f b = ∑ m, AddMonoidAlgebra.single m (e m b) := by sorry
