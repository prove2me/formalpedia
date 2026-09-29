-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_holRing_div_eq_theta
-- name    : CerednikDrinfeld.Omega.exists_holRing_div_eq_theta
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/f7f65659-f196-5a8a-b41b-f6b26b5ee3fc
-- title:
--   Theta product as a ratio of rigid-holomorphic functions
-- statement:
--   Let $K_0$ be a field and $K$ a field with decidable equality, complete and equipped with a valuation $v$ taking values in a linearly ordered commutative group with zero $\Gamma_0$, together with a $K_0$-algebra structure; write $\Omega = K \setminus \operatorname{image}(K_0 \to K)$ for the Drinfeld upper half plane `upperHalfPlane K₀ K`. Let $\varpi$ be a pseudo-uniformiser, i.e. an element of $K_0$ with $0 < v(\varpi) < 1$ such that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N$, and assume that the associated affinoids exhaust $\Omega$: every $z \in \Omega$ lies in `affinoid ϖ n` for some $n$. Let $\rho\colon G \to \mathrm{PGL}_2(K_0)$ be a homomorphism from a group $G$ which is discrete in the sense that for each $\varepsilon \in \Gamma_0$, $\varepsilon \ne 0$, only finitely many $\gamma$ admit a $\mathrm{GL}_2(K_0)$-lift $g$ of $\rho(\gamma)$ all of whose entries have valuation $\le 1$ and with $v(\det g) \ge \varepsilon$. Let $a, b, z_0 \in \Omega$, and assume $z_0$ lies in neither orbit, i.e. $\rho(\gamma)z_0' \ne z_0$ fails for no $\gamma$ in the precise form: $\mathrm{pmoebius}(\rho(\gamma))a \ne z_0$ and $\mathrm{pmoebius}(\rho(\gamma))b \ne z_0$ for all $\gamma \in G$. Then there exist $F, H$ in the ring `holRing ϖ` of functions $\Omega \to K$ whose restriction to each affinoid is a uniform limit of a uniformly bounded sequence of pole-free rational functions, such that $H$ is a non-zero-divisor of that ring, $H(z) = 0$ exactly for $z$ in the orbit $\{\mathrm{pmoebius}(\rho(\gamma))b\}_{\gamma \in G}$, $F(z) = 0$ exactly for $z$ in the orbit of $a$, and for every $z \in \Omega$ outside the orbit of $b$ one has $F(z)/H(z) = \Theta(z) = \prod'_{\gamma \in G} [\,z, z_0; \rho(\gamma)a, \rho(\gamma)b\,]$, the unconditional infinite product of the cross-ratio factors `thetaFactor ρ a b z₀ z γ`.
--
--   This is the construction of the Manin–Drinfeld cross-ratio theta function attached to a discrete subgroup of $\mathrm{PGL}_2(K_0)$, realised as a quotient of two rigid-holomorphic functions on the Drinfeld upper half plane with zero divisors the two orbits. It is the analytic input for the passage to theta functions as meromorphic functions and for their transformation behaviour under $G$ with multiplicative periods, used in the Čerednik–Drinfeld description of Mumford curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_holRing_div_eq_theta.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_holRing_div_eq_theta
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    {a b z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀) :
    ∃ F H : ↥(holRing ϖ),
      H ∈ nonZeroDivisors ↥(holRing ϖ) ∧
      (∀ z : ↥(upperHalfPlane K₀ K),
        (H : ↥(upperHalfPlane K₀ K) → K) z = 0 ↔ ∃ γ : G, pmoebius K₀ (ρ γ) b = (z : K)) ∧
      (∀ z : ↥(upperHalfPlane K₀ K),
        (F : ↥(upperHalfPlane K₀ K) → K) z = 0 ↔ ∃ γ : G, pmoebius K₀ (ρ γ) a = (z : K)) ∧
      (∀ z : ↥(upperHalfPlane K₀ K), (¬ ∃ γ : G, pmoebius K₀ (ρ γ) b = (z : K)) →
        (F : ↥(upperHalfPlane K₀ K) → K) z / (H : ↥(upperHalfPlane K₀ K) → K) z = theta ρ a b z₀ (z : K)) := by sorry
