-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_disc_of_mem_holOn
-- name    : CerednikDrinfeld.Omega.finite_setOf_apply_eq_zero_disc_of_mem_holOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/12f769ec-9517-5e47-aa7f-95341ca461ee
-- title:
--   Finiteness of zeros on a disc minus residue classes
-- statement:
--   Let $K$ be a field, complete and algebraically closed, carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, and assume the rank-one condition `hrk`: for all $x, y \in K$ with $v(x) < 1$ and $y \neq 0$ there is $n \in \mathbb{N}$ with $v(x)^n \le v(y)$. Let $S \subseteq K$ be a subset, let $c, \pi \in K$ with $\pi \neq 0$, and let $Z \subseteq K$ be a finite set such that $v(\pi) \le v(c - \zeta)$ for every $\zeta \in Z$. Assume $S$ contains the region $F$ of all $z \in K$ with $v(z - c) \le v(\pi)$ and $v(\pi) \le v(z - \zeta)$ for all $\zeta \in Z$, that is, the closed disc of radius $v(\pi)$ about $c$ with the open residue classes around the points of $Z$ removed. Let $f : S \to K$ belong to the subring `holOn K S`, so that there is a sequence $(r_k)$ of pairs of polynomials, each pole-free on $S$, with the associated values $r_k(z)$ bounded in valuation uniformly in $k$ and $z \in S$ by some $v(b)$, and with $z \mapsto r_k(z)$ tending to $f$ uniformly on $S$. Then either $f(z) = 0$ for every $z \in S$ lying in $F$, or the set of $z \in S$ lying in $F$ with $f(z) = 0$ is finite.
--
--   This is the finiteness-of-zeros statement (an identity principle in disjunctive form) for a rigid-analytic function on the basic affinoid piece of $\mathbb{P}^1$ used in the Čerednik–Drinfeld material: a closed disc with finitely many open residue classes deleted. It is invoked in the construction of rings of holomorphic functions with prescribed finite vanishing behaviour, and in the comparison of products of such functions on a disc.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_disc_of_mem_holOn.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.finite_setOf_apply_eq_zero_disc_of_mem_holOn
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (S : Set K) (c π : K) (hπ : π ≠ 0) (Z : Finset K) (hZ : ∀ ζ ∈ Z, Valued.v π ≤ Valued.v (c - ζ))
    (hS : ∀ z : K, Valued.v (z - c) ≤ Valued.v π → (∀ ζ ∈ Z, Valued.v π ≤ Valued.v (z - ζ)) → z ∈ S)
    {f : ↥S → K} (hf : f ∈ holOn K S) :
    (∀ z : ↥S, Valued.v ((z : K) - c) ≤ Valued.v π → (∀ ζ ∈ Z, Valued.v π ≤ Valued.v ((z : K) - ζ)) → f z = 0) ∨
      Set.Finite {z : ↥S | Valued.v ((z : K) - c) ≤ Valued.v π ∧
        (∀ ζ ∈ Z, Valued.v π ≤ Valued.v ((z : K) - ζ)) ∧ f z = 0} := by sorry
