-- Prove2me | Theorems.Thm_AddCommGroup_natCard_torsionBy_prod_eq_mul
-- name    : AddCommGroup.natCard_torsionBy_prod_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/0550b30e-631b-56e3-b913-015869f02f95
-- title:
--   Multiplicativity of N-torsion cardinality in a product
-- statement:
--   Let $A$ and $B$ be additive commutative groups, in arbitrary universes, and let $N$ be a natural number. Each group is regarded as a $\mathbb{Z}$-module, and for a $\mathbb{Z}$-module $M$ the submodule $\mathrm{torsionBy}\ \mathbb{Z}\ M\ (N : \mathbb{Z})$ consists of those $x \in M$ with $N \cdot x = 0$, i.e. the $N$-torsion subgroup $M[N]$. The assertion is the equality of natural numbers
--   $$\#\bigl((A \times B)[N]\bigr) = \#\bigl(A[N]\bigr)\cdot \#\bigl(B[N]\bigr),$$
--   where $\#$ denotes `Nat.card`, the cardinality of a type when it is finite and $0$ when it is infinite. No finiteness hypothesis is imposed on $A$ or $B$, and $N$ is unrestricted: for $N = 0$ the torsion subgroups are the whole groups, and for $N = 1$ they are trivial. With the `Nat.card` convention the statement is therefore also meaningful, and true, when one of the three torsion subgroups is infinite, both sides then being $0$.
--
--   This is the elementary multiplicativity of the $N$-torsion functor on finite direct products of abelian groups, in the cardinality form needed when counting torsion. It is used in the proof that an abelian group admitting suitable homomorphisms to cyclic groups of prime-power order is isomorphic to a product of such groups ([`AddEquiv.nonempty_addEquiv_pi_zmod_of_prod_addMonoidHom_zmod`](thm.html#AddEquiv.nonempty_addEquiv_pi_zmod_of_prod_addMonoidHom_zmod)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddCommGroup_natCard_torsionBy_prod_eq_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem AddCommGroup.natCard_torsionBy_prod_eq_mul
    (A : Type u) (B : Type v) [AddCommGroup A] [AddCommGroup B] (N : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (A × B) (N : ℤ)) =
      Nat.card (Submodule.torsionBy ℤ A (N : ℤ)) * Nat.card (Submodule.torsionBy ℤ B (N : ℤ)) := by sorry
