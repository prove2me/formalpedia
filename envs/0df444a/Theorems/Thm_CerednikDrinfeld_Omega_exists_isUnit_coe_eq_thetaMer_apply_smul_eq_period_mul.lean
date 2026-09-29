-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul
-- name    : CerednikDrinfeld.Omega.exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/26855f7e-719e-57ff-96f6-c5a34c88bcc9
-- title:
--   The theta function Theta(a,α a;z₀;·) is a holomorphic unit
-- statement:
--   Let $K_0$ be a field and $K$ a complete valued field (value group $\Gamma_0$) equipped with a $K_0$-algebra structure, and let $\varpi$ be a pseudo-uniformiser: an element of $K_0$ whose image in $K$ has valuation strictly between $0$ and $1$ and such that every nonzero element of $K_0$ has valuation between $v(\varpi)^N$ and $v(\varpi)^{-N}$ for some $N$. Assume `IsExhausted`, i.e. every point of $\Omega = K \setminus \operatorname{im}(K_0 \to K)$ lies in one of the affinoids `affinoid ϖ n`. Let $\rho : G \to \mathrm{PGL}_2(K_0)$ be a homomorphism from a group $G$ which is discrete in the sense that for each $\varepsilon \neq 0$ in $\Gamma_0$ only finitely many $\gamma$ admit a lift $g \in \mathrm{GL}_2(K_0)$ of $\rho\gamma$ with all entries of valuation $\le 1$ and $v(\det g) \ge \varepsilon$. Let $a, z_0 \in \Omega$ with $z_0$ outside the orbit $\{\rho(\gamma)a\}$ (Möbius action through `pmoebius`), and let $\alpha \in G$. Then there is an element $U$ of `holRing ϖ`, the ring of functions $\Omega \to K$ whose restriction to each affinoid is a uniform limit of uniformly bounded pole-free rational functions, such that: $U$ is a unit of that ring; the image of $U$ in the fraction field `merField ϖ` is $\Theta^{\mathrm{mer}}(a, \rho(\alpha)a; z_0)$, i.e. `thetaMer ϖ ρ a (pmoebius K₀ (ρ α) a) z₀`; for every $z \in \Omega$ not of the form $\rho(\gamma)a$, $U(z)$ equals the value $\Theta(a,\rho(\alpha)a;z_0;z)$ of the infinite product of cross-ratios $\prod'_{\gamma} [z, z_0; \rho(\gamma)a, \rho(\gamma)\rho(\alpha)a]$; and for all $\beta \in G$ and $z \in \Omega$, $U(\rho(\beta)\cdot z) = Q(\alpha,\beta)\, U(z)$, where $Q(\alpha,\beta) =$ `period ρ a z₀ α β` $= \Theta(a,\rho(\alpha)a;z_0;\rho(\beta)z_0)$.
--
--   This is the statement that the basic theta function attached to the divisor $(a) - (\rho(\alpha)a)$ is an invertible rigid-holomorphic function $u_\alpha$ on Drinfeld's upper half plane, automorphic with multiplier the Manin–Drinfeld period $Q(\alpha, \cdot)$; the zero and pole orbits coincide, so the a priori meromorphic `thetaMer` is represented by a unit. It is used in the subsequent study of the period pairing $Q$ and of valuations of products of theta functions in the Cerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul.lean

import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    {a z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (α : G) :
    ∃ U : ↥(holRing ϖ), IsUnit U ∧
      algebraMap ↥(holRing ϖ) (merField ϖ) U = thetaMer ϖ ρ a (pmoebius K₀ (ρ α) a) z₀ ∧
      (∀ z : ↥(upperHalfPlane K₀ K), (¬ ∃ γ : G, pmoebius K₀ (ρ γ) a = (z : K)) →
        (U : ↥(upperHalfPlane K₀ K) → K) z = theta ρ a (pmoebius K₀ (ρ α) a) z₀ (z : K)) ∧
      ∀ (β : G) (z : ↥(upperHalfPlane K₀ K)),
        (U : ↥(upperHalfPlane K₀ K) → K) ((ρ β) • z) = period ρ a z₀ α β * (U : ↥(upperHalfPlane K₀ K) → K) z := by sorry
