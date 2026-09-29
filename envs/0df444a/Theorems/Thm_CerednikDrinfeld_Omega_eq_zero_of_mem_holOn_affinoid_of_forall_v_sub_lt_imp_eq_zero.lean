-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero
-- name    : CerednikDrinfeld.Omega.eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/5ac72736-cf1d-5ecc-8c90-a908aa7e8f36
-- title:
--   Identity principle on a Drinfeld affinoid
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra which is a field, carrying a valuation $v =$ `Valued.v` with values in a linearly ordered commutative group with zero $\Gamma_0$, complete and algebraically closed. Let $\varpi$ be a pseudo-uniformiser of $K_0$ relative to $K$, i.e. an element $\varpi \in K_0$ with $0 < v(\varpi) < 1$ (valuations of images under $\mathrm{algebraMap}$) such that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N \in \mathbb{N}$. Assume the rank-one condition `hrk`: for all $x, y \in K$ with $v(x) < 1$ and $y \neq 0$ there is $n$ with $v(x)^n \le v(y)$. Fix $n \in \mathbb{N}$ and assume `hfin`: there is a finite set $T \subseteq K_0$ such that every $a \in K_0$ with $v(a) \le v(\varpi)^{-n}$ satisfies $v(a - t) < v(\varpi)^n$ for some $t \in T$. Let $\Omega_n =$ `affinoid ϖ n` be the set of $z \in K$ with $v(z) \le v(\varpi)^{-n}$ and $v(z - a) \ge v(\varpi)^n$ for every $a \in K_0$ with $v(a) \le v(\varpi)^{-n}$. Let $g : \Omega_n \to K$ lie in the subring `holOn K (affinoid ϖ n)`, that is, $g$ is the uniform limit on $\Omega_n$ of a sequence of rational pairs $r_k$, each pole-free on $\Omega_n$, whose evaluations are uniformly bounded by $v(b)$ for a single $b \in K$. Suppose there are $z_0 \in \Omega_n$ and $c \in K$, $c \neq 0$, such that $g(z) = 0$ for every $z \in \Omega_n$ with $v(z - z_0) < v(c)$. Then $g = 0$.
--
--   This is the identity theorem for holomorphic functions on a single affinoid $\Omega_n$ of Drinfeld's $p$-adic upper half plane, an affinoid of the shape 'closed disc minus finitely many open discs': vanishing on a ball of positive radius, the radius being a value $v(c)$ of a nonzero element of $K$ rather than an arbitrary element of $\Gamma_0$, forces vanishing throughout. It is proved by propagating vanishing along discs and annuli via [`CerednikDrinfeld.Omega.RatPair.identityPrinciple_disc`](thm.html#CerednikDrinfeld.Omega.RatPair.identityPrinciple_disc) and [`CerednikDrinfeld.Omega.RatPair.identityPrinciple_annulus`](thm.html#CerednikDrinfeld.Omega.RatPair.identityPrinciple_annulus), and is used downstream to extract orders of vanishing and factorisations of holomorphic functions on $\Omega_n$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (n : ℕ)
    (hfin : ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {g : ↥(affinoid ϖ n) → K} (hg : g ∈ holOn K (affinoid ϖ n))
    {z₀ : K} (hz₀ : z₀ ∈ affinoid ϖ n) {c : K} (hc : c ≠ 0)
    (h0 : ∀ z : ↥(affinoid ϖ n), Valued.v ((z : K) - z₀) < Valued.v c → g z = 0) :
    g = 0 := by sorry
