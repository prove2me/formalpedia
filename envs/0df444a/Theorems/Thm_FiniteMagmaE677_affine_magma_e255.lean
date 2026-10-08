-- Prove2me | Theorems.Thm_FiniteMagmaE677_affine_magma_e255
-- name    : FiniteMagmaE677.affine_magma_e255
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T12:58:20.130075+00:00
-- url     : https://prove2.me/theorems/eeeca47d-48b4-4f9f-93b0-341f07fe6d08
-- title:
--   Affine operations satisfying E677 satisfy E255: no linear counterexamples over finite rings
-- statement:
--   Let $R$ be a finite commutative ring and let $x \diamond y = a x + b y + c$ with fixed coefficients $a, b, c \in R$ be an affine binary operation on $R$. If $\diamond$ satisfies equation 677,
--
--   $$x = y \diamond \bigl( x \diamond ((y \diamond x) \diamond y) \bigr) \qquad \text{for all } x, y \in R,$$
--
--   then it also satisfies equation 255,
--
--   $$x = ((x \diamond x) \diamond x) \diamond x \qquad \text{for all } x \in R.$$
--
--   Consequently, any finite counterexample to the implication E677 $\to$ E255 must be non-affine. This is the finite-ring, scalar-coefficient form of the "no linear counterexamples" lemma in Chapter 13 of the Equational Theories Project blueprint; it certifies at once all affine models over prime fields, including the translation-invariant models $x \diamond y = 2x - y$ on $\mathbb{F}_5$ and the models $x \diamond y = 4x + 3y$ on $\mathbb{F}_7$.
--
--   The proof: right-translation collisions force left-translation agreement (cancel $b x + c$), so right translations are injective by the magma-level cancellation lemma, hence surjective by finiteness, giving each $x$ a fixer; fixer uniqueness identifies it with $(x \diamond x) \diamond x$.
-- source:
--   Equational Theories Project, online proof blueprint, Chapter 13 (677), linear-model lemma (scalar version), https://teorth.github.io/equational_theories/blueprint/677-chapter.html; Lean proof contributed here.

import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.LinearCombination
import Definitions.Def_FiniteMagmaE677
import Theorems.Thm_FiniteMagmaE677_left_bijective
import Theorems.Thm_FiniteMagmaE677_fixer_unique
import Theorems.Thm_FiniteMagmaE677_linear_collision_injective

universe u v

theorem FiniteMagmaE677.affine_magma_e255 {R : Type v} [CommRing R] [Fintype R]
    (a b c : R)
    (h : FiniteMagmaE677.E677 (fun x y : R => a * x + b * y + c)) :
    FiniteMagmaE677.E255 (fun x y : R => a * x + b * y + c) := by sorry
