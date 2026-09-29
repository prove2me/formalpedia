-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder
-- name    : CerednikDrinfeld.Omega.theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/1a1fda0e-5eca-5133-aa37-1cc53a6ee65e
-- title:
--   Trivial theta multiplier at torsion elements
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra which is a field, carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, and assume $K$ is complete and algebraically closed (decidable equality on $K$ is assumed as an instance). Let $\varpi$ be a pseudo-uniformizer, i.e. an element $\varpi \in K_0$ with $0 < v(\varpi) < 1$ such that for every $a \neq 0$ in $K_0$ there is $N$ with $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$; assume `IsExhausted` for $\varpi$, that is, every point of the Drinfeld upper half plane $\Omega = K \setminus \mathrm{image}(K_0 \to K)$ lies in one of the affinoids $\mathrm{affinoid}\ \varpi\ n$, and assume that the ring `holRing` $\varpi$ of functions $\Omega \to K$ whose restriction to each such affinoid is a uniform limit of uniformly bounded pole-free rational functions is a domain. Let $G$ be a group and $\rho : G \to \mathrm{PGL}_2(K_0)$ a homomorphism which is discrete in the sense that for each $\varepsilon \neq 0$ in $\Gamma_0$ only finitely many $\gamma \in G$ admit a lift $g \in \mathrm{GL}_2(K_0)$ of $\rho(\gamma)$ with all entries of value $\le 1$ and $v(\det g) \ge \varepsilon$. Let $a, b, z_0 \in \Omega$ be such that no $\rho$-translate $\mathrm{pmoebius}(\rho\delta)(a)$ or $\mathrm{pmoebius}(\rho\delta)(b)$ equals $z_0$, where $\mathrm{pmoebius}$ denotes the Möbius action of $\mathrm{PGL}_2(K_0)$ on $\mathbb{P}^1(K)$ read in the affine coordinate. Then for every $\gamma \in G$ of finite order the unconditional product $\mathrm{theta}\ \rho\ a\ b\ z_0\ z = \prod_{\delta \in G}' [z, z_0; \rho(\delta)a, \rho(\delta)b]$ of cross-ratios, evaluated at $z = \mathrm{pmoebius}(\rho\gamma)(z_0)$, equals $1$.
--
--   This is the statement that the automorphy factor of the theta function $\Theta(a,b;z_0;\cdot)$ attached to a discrete projective action is trivial on torsion elements of $G$, in the Mumford–Čerednik–Drinfeld uniformisation of the relevant curves. It is used in the construction of the period/theta data on the degree-zero Picard group of a Mumford quotient, where theta multipliers of elements of finite order must be shown to vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder.lean

import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.OrderOfElement

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega
open CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Omega.theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) [IsDomain ↥(holRing ϖ)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    {a b z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀)
    (γ : G) (hγ : IsOfFinOrder γ) :
    theta ρ a b z₀ (pmoebius K₀ (ρ γ) z₀) = 1 := by sorry
