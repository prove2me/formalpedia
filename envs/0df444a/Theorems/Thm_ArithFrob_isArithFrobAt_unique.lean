-- Prove2me | Theorems.Thm_ArithFrob_isArithFrobAt_unique
-- name    : ArithFrob.isArithFrobAt_unique
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/e6f557b3-d976-55d7-9240-3f08f6770a31
-- title:
--   Uniqueness of arithmetic Frobenius at trivial inertia
-- statement:
--   Let $A$ and $B$ be commutative rings with $B$ an $A$-algebra, and let $G$ be a group acting on $B$ by ring automorphisms in such a way that the action commutes with the $A$-scalar multiplication on $B$. Let $P$ be a maximal ideal of $B$ whose contraction $P \cap A$ (written `P.under A`) is a maximal ideal of $A$, and assume the residue ring $A/(P\cap A)$ is finite, of cardinality $q =$ `Nat.card (A ⧸ P.under A)`, and that $B/P$ is finite as well. Let $\sigma_1,\sigma_2 \in G$ each be an arithmetic Frobenius element at $P$ in Mathlib's sense `IsArithFrobAt A σ P`, i.e. $\sigma_i \cdot x \equiv x^{q} \pmod P$ for every $x \in B$. Assume finally that the inertia subgroup `P.inertia G` of $P$ in $G$ is trivial. Then $\sigma_1 = \sigma_2$. Only uniqueness is asserted: no existence statement, and nothing about ideals with nontrivial inertia.
--
--   This is the standard uniqueness half of the theory of the Frobenius element: at a maximal ideal with trivial inertia the Frobenius congruence determines the group element, so the notation $\mathrm{Frob}_P$ is unambiguous. It is used in the Langlands–Tunnell part of the development, where Frobenius elements attached to maximal ideals must be compared across conjugate or equal residue data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ArithFrob_isArithFrobAt_unique.lean

import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.NumberTheory.RamificationInertia.Galois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MulAction
open scoped Pointwise

theorem ArithFrob.isArithFrobAt_unique {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    {P : Ideal B} [P.IsMaximal] [(P.under A).IsMaximal]
    [Fintype (A ⧸ P.under A)] [Finite (B ⧸ P)]
    {σ₁ σ₂ : G} (h₁ : IsArithFrobAt A σ₁ P) (h₂ : IsArithFrobAt A σ₂ P)
    (hin : P.inertia G = ⊥) : σ₁ = σ₂ := by sorry
