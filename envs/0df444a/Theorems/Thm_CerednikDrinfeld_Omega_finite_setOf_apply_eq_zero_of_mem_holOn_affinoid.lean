-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_of_mem_holOn_affinoid
-- name    : CerednikDrinfeld.Omega.finite_setOf_apply_eq_zero_of_mem_holOn_affinoid
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/c3d25e3a-a1f6-58a3-816b-79a4afddb292
-- title:
--   Finiteness of the zero set on the affinoid Ωₙ
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra which is a field, equipped with a valuation $v =$ `Valued.v` taking values in a linearly ordered commutative group with zero $\Gamma_0$, and assume $K$ is complete and algebraically closed. Let $\varpi$ be a pseudo-uniformiser of $K_0$ relative to $K$, that is, an element $\varpi.\varpi \in K_0$ with $0 < v(\varpi) < 1$ in $K$ (writing $v(\varpi)$ for the valuation of its image under $\mathrm{algebraMap}\,K_0\,K$) such that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N \in \mathbb{N}$. Assume the rank-one condition `hrk`: for all $x, y \in K$ with $v(x) < 1$ and $y \neq 0$ there is $m \in \mathbb{N}$ with $v(x)^m \le v(y)$. Fix $n \in \mathbb{N}$ and assume `hfin`: there is a finite set $T \subseteq K_0$ such that every $a \in K_0$ with $v(a) \le v(\varpi)^{-n}$ satisfies $v(a - t) < v(\varpi)^n$ for some $t \in T$. Let $\mathrm{affinoid}\,\varpi\,n$ be the set of $z \in K$ with $v(z) \le v(\varpi)^{-n}$ and $v(\varpi)^n \le v(z - a)$ for every $a \in K_0$ with $v(a) \le v(\varpi)^{-n}$. Let $f$ be a $K$-valued function on this set lying in the subring $\mathrm{holOn}$, i.e. there is a sequence of rational pairs $r_k$, each pole-free on the affinoid, with $v(r_k(z)) \le v(b)$ for some fixed $b \in K$ and all $k$ and all $z$, converging uniformly to $f$. If $f$ is not the zero function, then $\{z \in \mathrm{affinoid}\,\varpi\,n \mid f(z) = 0\}$ is finite.
--
--   This is the finiteness-of-zeros half of the identity principle for holomorphic functions on the standard affinoids $\Omega_n$ exhausting Drinfeld's upper half plane: a nonzero uniform limit of bounded pole-free rational functions on $\Omega_n$ has only finitely many zeros there. It underlies the divisor calculus on $\Omega_n$, and is cited in the construction of the factorisation of such a function into a product of linear factors and in the vanishing criteria [`CerednikDrinfeld.Omega.eq_zero_of_forall_finite_forall_apply_eq_zero`](thm.html#CerednikDrinfeld.Omega.eq_zero_of_forall_finite_forall_apply_eq_zero) and [`CerednikDrinfeld.Omega.dvd_of_forall_ordAt_le`](thm.html#CerednikDrinfeld.Omega.dvd_of_forall_ordAt_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_of_mem_holOn_affinoid.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.finite_setOf_apply_eq_zero_of_mem_holOn_affinoid
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (n : ℕ)
    (hfin : ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {f : ↥(affinoid ϖ n) → K} (hf : f ∈ holOn K (affinoid ϖ n)) (hne : f ≠ 0) :
    Set.Finite {z : ↥(affinoid ϖ n) | f z = 0} := by sorry
