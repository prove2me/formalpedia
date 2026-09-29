-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_theta_smul_eq_one_of_isOfFinOrder
-- name    : CerednikDrinfeld.Omega.theta_smul_eq_one_of_isOfFinOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/94c82370-87c9-5791-a8de-c7c52443b87b
-- title:
--   Theta function attached to a torsion element is 1
-- statement:
--   Let $K_0$ be a field and $K$ a field extension algebra over $K_0$ carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, and assume $K$ is complete and algebraically closed. Let $\varpi$ be a pseudo-uniformizer, i.e. an element of $K_0$ with $0 < v(\varpi) < 1$ such that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N \in \mathbb{N}$, and assume $\varpi$ is exhausting: every point of the Drinfeld upper half-plane $\Omega = K \setminus \mathrm{image}(K_0 \to K)$ lies in one of the affinoids $\{z : v(z) \le v(\varpi)^{-n},\ v(z - a) \ge v(\varpi)^{n}\ \text{for all } a \in K_0 \text{ with } v(a) \le v(\varpi)^{-n}\}$. Assume moreover that `holRing` $\varpi$ — the ring of functions on $\Omega$ whose restriction to each affinoid is a uniform limit of a uniformly bounded sequence of rational functions without poles there — is a domain. Let $\rho : G \to \mathrm{PGL}_2(K_0)$ be a homomorphism from a group $G$ which is discrete in the sense that, for every $\varepsilon \ne 0$ in $\Gamma_0$, only finitely many $\gamma \in G$ admit a lift $g \in \mathrm{GL}_2(K_0)$ of $\rho(\gamma)$ with all entries of valuation at most $1$ and $v(\det g) \ge \varepsilon$. Let $\alpha \in G$ be of finite order, and let $p, w, z \in \Omega$ be such that neither $w$ nor $z$ lies in the orbit $\{\rho(\gamma)p : \gamma \in G\}$ under the Möbius action of $\mathrm{PGL}_2(K_0)$ on $K$ (via the one-point extension). Then the theta value $\Theta(p, \rho(\alpha)p; w)(z)$, the product over $\gamma \in G$ of the cross ratios of $z$, $w$, $\rho(\gamma)p$ and $\rho(\gamma)\rho(\alpha)p$, equals $1$.
--
--   This is the vanishing of the Manin–Drinfeld theta multiplier attached to a torsion (elliptic) element of a discrete group acting on the Drinfeld upper half-plane: the divisor $(\rho(\alpha)p) - (p)$ of a finite-order element contributes trivially. It feeds the statement [`CerednikDrinfeld.Omega.theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder`](thm.html#CerednikDrinfeld.Omega.theta_apply_pmoebius_basePoint_eq_one_of_isOfFinOrder) in the theta-function apparatus underlying the Mumford/Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_theta_smul_eq_one_of_isOfFinOrder.lean

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

theorem CerednikDrinfeld.Omega.theta_smul_eq_one_of_isOfFinOrder
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) [IsDomain ↥(holRing ϖ)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (α : G) (hα : IsOfFinOrder α)
    {p w z : K} (hp : p ∈ upperHalfPlane K₀ K) (hw : w ∈ upperHalfPlane K₀ K) (hz : z ∈ upperHalfPlane K₀ K)
    (hwp : ∀ γ : G, pmoebius K₀ (ρ γ) p ≠ w) (hzp : ∀ γ : G, pmoebius K₀ (ρ γ) p ≠ z) :
    theta ρ p (pmoebius K₀ (ρ α) p) w z = 1 := by sorry
