-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_mem_upperHalfPlane_forall_pmoebius_ne_and_of_countable_of_archimedean
-- name    : CerednikDrinfeld.Omega.exists_mem_upperHalfPlane_forall_pmoebius_ne_and_of_countable_of_archimedean
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/fd5a29fd-8d4b-5ec9-ab5b-64058ed3f569
-- title:
--   A point of Ω avoiding two countable orbits
-- statement:
--   Let $K_0$ be a field and $K$ a field that is a $K_0$-algebra, carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$ and complete for the induced topology. Suppose given a pseudo-uniformiser $\varpi$ of $K_0$ in $K$, that is, an element $\varpi \in K_0$ with $0 < v(\varpi) < 1$ in $K$ and such that for every nonzero $a \in K_0$ there is $N \in \mathbb{N}$ with $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ (valuations taken of the images in $K$). Assume further the archimedean property `hrk`: for all $x, y \in K$ with $v(x) < 1$ and $y \ne 0$ there is $n \in \mathbb{N}$ with $v(x)^n \le v(y)$. Let $G$ be a countable group and $\rho : G \to \mathrm{PGL}_2(K_0)$ a group homomorphism, and let $a, b$ lie in Drinfeld's upper half plane $\Omega = K \setminus \operatorname{im}(K_0 \to K)$, the complement of the range of the structure map. Then there exists $z_0 \in \Omega$ such that $\mathrm{pmoebius}(\rho\gamma)(a) \ne z_0$ and $\mathrm{pmoebius}(\rho\gamma)(b) \ne z_0$ for every $\gamma \in G$, where `pmoebius` sends $z$ to the affine coordinate of the image of $z \in \mathbb{P}^1(K)$ under the given element of $\mathrm{PGL}_2(K_0)$, the point at infinity being sent to $0$.
--
--   This is the elementary cardinality statement that $\Omega$, being uncountable, contains a point outside the union of the two $\rho(G)$-orbits of $a$ and $b$; the hypotheses on $\varpi$ and the archimedean property serve to guarantee that the valuation topology on $K$ is non-discrete, so that $\Omega$ is uncountable. It provides the admissible base point $z_0$ in the construction of the theta function $\Theta(a,b;z_0;\cdot)$ attached to a discrete subgroup of $\mathrm{PGL}_2(K_0)$, and is used in the construction of holomorphic functions with prescribed orders along a $\Gamma$-orbit and in the description of degree-zero divisor classes on Mumford quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_mem_upperHalfPlane_forall_pmoebius_ne_and_of_countable_of_archimedean.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_mem_upperHalfPlane_forall_pmoebius_ne_and_of_countable_of_archimedean
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    {G : Type} [Group G] [Countable G] (ρ : G →* PGL(2, K₀))
    {a b : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) :
    ∃ z₀ : K, z₀ ∈ upperHalfPlane K₀ K ∧
      (∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) ∧ (∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀) := by sorry
