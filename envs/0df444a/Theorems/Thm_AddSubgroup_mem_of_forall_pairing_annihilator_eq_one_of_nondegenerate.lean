-- Prove2me | Theorems.Thm_AddSubgroup_mem_of_forall_pairing_annihilator_eq_one_of_nondegenerate
-- name    : AddSubgroup.mem_of_forall_pairing_annihilator_eq_one_of_nondegenerate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/c1fb549b-cd33-5cad-8d44-30abcef25bff
-- title:
--   Double annihilator of a subgroup under a non-degenerate pairing
-- statement:
--   Let $G$ be a finite additive abelian group, $L$ a field, and $n$ a natural number with $n \neq 0$. Let $B \colon G \times G \to L$ be a function of two variables such that: $B(x,y)^n = 1$ for all $x, y \in G$; $B$ is additive-to-multiplicative in the first variable, $B(x + x', y) = B(x,y)B(x',y)$; likewise in the second variable, $B(x, y + y') = B(x,y)B(x,y')$; $B$ is non-degenerate on the left, i.e. any $x$ with $B(x,y) = 1$ for all $y$ is zero; and non-degenerate on the right, i.e. any $y$ with $B(x,y) = 1$ for all $x$ is zero. Let $A$ be an additive subgroup of $G$ and $x \in G$. Assume that for every $y \in G$, if $B(a,y) = 1$ for all $a \in A$ then $B(x,y) = 1$; that is, $x$ annihilates the annihilator of $A$. The conclusion is $x \in A$, so that the double annihilator of $A$ equals $A$.
--
--   This is the standard statement that for a bi-multiplicative non-degenerate pairing of a finite abelian group with values in the roots of unity of a field, a subgroup coincides with its double annihilator. It is used in the construction of the Weil-type pairings on torsion of Jacobians of modular curves, where annihilator descriptions of Galois-, Hecke- and diamond-stable subgroups are needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddSubgroup_mem_of_forall_pairing_annihilator_eq_one_of_nondegenerate.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AddSubgroup.mem_of_forall_pairing_annihilator_eq_one_of_nondegenerate
    {G : Type} [AddCommGroup G] [Finite G] {L : Type} [Field L] (n : ℕ) (hn : n ≠ 0)
    (B : G → G → L)
    (hval : ∀ x y : G, B x y ^ n = 1)
    (hadd₁ : ∀ x x' y : G, B (x + x') y = B x y * B x' y)
    (hadd₂ : ∀ x y y' : G, B x (y + y') = B x y * B x y')
    (hleft : ∀ x : G, (∀ y : G, B x y = 1) → x = 0)
    (hright : ∀ y : G, (∀ x : G, B x y = 1) → y = 0)
    (A : AddSubgroup G) (x : G)
    (hx : ∀ y : G, (∀ a ∈ A, B a y = 1) → B x y = 1) :
    x ∈ A := by sorry
