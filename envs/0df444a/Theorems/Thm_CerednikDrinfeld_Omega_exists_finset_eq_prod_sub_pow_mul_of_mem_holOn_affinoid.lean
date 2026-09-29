-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_affinoid
-- name    : CerednikDrinfeld.Omega.exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_affinoid
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/e9190e2a-7176-54e0-854e-11be03a8a306
-- title:
--   Weierstrass factorisation on an affinoid of Ω
-- statement:
--   Let $K_0$ be a field and $K$ a field which is a $K_0$-algebra, equipped with decidable equality, carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, and assume $K$ is complete and algebraically closed. Let $\varpi$ be a pseudo-uniformiser: an element $\varpi.\varpi \in K_0$ with $0 < v(\varpi) < 1$ in $K$ and such that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N \in \mathbb{N}$ (here $v(\varpi)$ abbreviates the valuation of the image of $\varpi.\varpi$ in $K$). Assume the Archimedean condition `hrk`: for all $x, y \in K$ with $v(x) < 1$ and $y \neq 0$ there is $n$ with $v(x)^n \le v(y)$. Fix $n \in \mathbb{N}$ and assume `hfin`: there is a finite set $T \subseteq K_0$ such that every $a \in K_0$ with $v(a) \le v(\varpi)^{-n}$ satisfies $v(a - t) < v(\varpi)^n$ for some $t \in T$. Write $\Omega_n =$ `affinoid ϖ n` for the set of $z \in K$ with $v(z) \le v(\varpi)^{-n}$ and $v(z - a) \ge v(\varpi)^n$ for every $a \in K_0$ with $v(a) \le v(\varpi)^{-n}$. Let $f : \Omega_n \to K$ lie in the subring `holOn`, that is, $f$ is the uniform limit on $\Omega_n$ of a sequence of rational functions each pole-free on $\Omega_n$ and with evaluations uniformly bounded in valuation, and suppose $f(z) \neq 0$ for some $z \in \Omega_n$. Then there exist a finite set $Z$ of points of $\Omega_n$, a function $k : \Omega_n \to \mathbb{N}$ and $u : \Omega_n \to K$ such that $u$ again lies in `holOn`, $u$ vanishes nowhere on $\Omega_n$, a point $p$ lies in $Z$ if and only if $k(p) \ge 1$, and $f(z) = \bigl(\prod_{p \in Z} (z - p)^{k(p)}\bigr) u(z)$ for every $z \in \Omega_n$. That $Z$ is precisely the zero set of $f$ and $k(p)$ the order of vanishing is not asserted, though it follows from the displayed identity together with the non-vanishing of $u$.
--
--   This is the Weierstrass-type factorisation of a nonzero rigid analytic function on the affinoid $\Omega_n$ of Drinfeld's upper half-plane: the function splits as a polynomial supported on its zeros times a unit of the ring of holomorphic functions. It feeds the construction of invariant theta-like functions on $\Omega$, being used in [`CerednikDrinfeld.Omega.exists_holRing_forall_finite_mul_eq_of_forall_exists_mem_holOn_affinoid_mul_eq_of_invariant`](thm.html#CerednikDrinfeld.Omega.exists_holRing_forall_finite_mul_eq_of_forall_exists_mem_holOn_affinoid_mul_eq_of_invariant).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_affinoid.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_finset_eq_prod_sub_pow_mul_of_mem_holOn_affinoid
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (n : ℕ)
    (hfin : ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {f : ↥(affinoid ϖ n) → K} (hf : f ∈ holOn K (affinoid ϖ n)) (hne : ∃ z : ↥(affinoid ϖ n), f z ≠ 0) :
    ∃ (Z : Finset ↥(affinoid ϖ n)) (k : ↥(affinoid ϖ n) → ℕ) (u : ↥(affinoid ϖ n) → K),
      u ∈ holOn K (affinoid ϖ n) ∧ (∀ z : ↥(affinoid ϖ n), u z ≠ 0) ∧
      (∀ p : ↥(affinoid ϖ n), p ∈ Z ↔ 1 ≤ k p) ∧
      ∀ z : ↥(affinoid ϖ n), f z = (∏ p ∈ Z, ((z : K) - (p : K)) ^ k p) * u z := by sorry
