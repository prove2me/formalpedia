-- Prove2me | Theorems.Thm_AddSubgroup_forall_mem_of_forall_pairing_eq_one_of_natCard_mul_eq
-- name    : AddSubgroup.forall_mem_of_forall_pairing_eq_one_of_natCard_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/a3281f40-4f92-5231-a6ac-218853b4a5f1
-- title:
--   Isotropic subgroups of complementary order are mutual annihilators
-- statement:
--   Let $G$ be a finite additive abelian group, $L$ a field of characteristic zero, $n$ a nonzero natural number and $B \colon G \times G \to L$ a function such that: $B(x,y)^n = 1$ for all $x,y \in G$; $B$ is additive-to-multiplicative in each variable, i.e. $B(x+x',y) = B(x,y)B(x',y)$ and $B(x,y+y') = B(x,y)B(x,y')$ for all arguments; and $B$ is non-degenerate on both sides, i.e. $B(x,y)=1$ for all $y$ forces $x=0$, and $B(x,y)=1$ for all $x$ forces $y=0$. Let $T$ and $F$ be subgroups of $G$ which pair trivially, $B(t,f)=1$ for all $t \in T$ and $f \in F$, and whose orders satisfy $\#T \cdot \#F = \#G$ (cardinalities taken as `Nat.card` of the coercions). The conclusion is the pair of inclusions: every $x \in G$ with $B(x,f)=1$ for all $f \in F$ lies in $T$, and every $y \in G$ with $B(t,y)=1$ for all $t \in T$ lies in $F$. Thus only the inclusions of annihilators into $T$ and $F$ are asserted; the opposite inclusions are exactly the triviality hypothesis on the pairing between $T$ and $F$.
--
--   This is the standard orthogonality criterion for a perfect $\mu_n$-valued pairing on a finite abelian group: two subgroups that pair trivially and whose orders multiply to $\#G$ are each other's full annihilators. It is used in the analysis of the Néron model of $J_H$ at a prime of bad reduction, to identify the toric part and the finite part of the $m$-torsion as mutual annihilators under the Weil pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddSubgroup_forall_mem_of_forall_pairing_eq_one_of_natCard_mul_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AddSubgroup.forall_mem_of_forall_pairing_eq_one_of_natCard_mul_eq
    {G : Type} [AddCommGroup G] [Finite G] {L : Type} [Field L] [CharZero L] (n : ℕ) (hn : n ≠ 0)
    (B : G → G → L)
    (hval : ∀ x y : G, B x y ^ n = 1)
    (hadd₁ : ∀ x x' y : G, B (x + x') y = B x y * B x' y)
    (hadd₂ : ∀ x y y' : G, B x (y + y') = B x y * B x y')
    (hleft : ∀ x : G, (∀ y : G, B x y = 1) → x = 0)
    (hright : ∀ y : G, (∀ x : G, B x y = 1) → y = 0)
    (T F : AddSubgroup G) (hiso : ∀ t ∈ T, ∀ f ∈ F, B t f = 1)
    (hcard : Nat.card T * Nat.card F = Nat.card G) :
    (∀ x : G, (∀ f ∈ F, B x f = 1) → x ∈ T) ∧ (∀ y : G, (∀ t ∈ T, B t y = 1) → y ∈ F) := by sorry
