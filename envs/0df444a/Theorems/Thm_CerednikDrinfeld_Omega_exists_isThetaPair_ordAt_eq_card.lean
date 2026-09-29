-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_isThetaPair_ordAt_eq_card
-- name    : CerednikDrinfeld.Omega.exists_isThetaPair_ordAt_eq_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/bcd76abd-a0d3-5d88-b54e-0ba029b507d0
-- title:
--   Orders of vanishing of a theta pair on Ω
-- statement:
--   Let $K_0$ be a field and $K$ a field extension-algebra over $K_0$ with decidable equality, equipped with a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, complete and algebraically closed. Let $\varpi$ be a pseudo-uniformizer: an element $\varpi.\varpi \in K_0$ with $0 < v(\varpi.\varpi) < 1$ such that every nonzero $a \in K_0$ satisfies $v(\varpi.\varpi)^N \le v(a) \le v(\varpi.\varpi)^{-N}$ for some $N$. Three hypotheses on the valued field are imposed: `hrk`, that for $x$ with $v(x)<1$ and $y \ne 0$ some power $v(x)^n \le v(y)$; `hex`, that every point of $\Omega = K \setminus \mathrm{image}(K_0 \to K)$ lies in one of the affinoids $\mathrm{affinoid}\ \varpi\ n = \{z : v(z) \le v(\varpi.\varpi)^{-n} \text{ and } v(z-a) \ge v(\varpi.\varpi)^{n} \text{ for all } a \in K_0 \text{ with } v(a) \le v(\varpi.\varpi)^{-n}\}$; and `hfin`, that for each $n$ there is a finite $T \subseteq K_0$ with every $a \in K_0$ of valuation $\le v(\varpi.\varpi)^{-n}$ within distance $< v(\varpi.\varpi)^{n}$ of some $t \in T$. Let $G$ be a group and $\rho : G \to \mathrm{PGL}_2(K_0)$ a homomorphism which is discrete in the sense that for every $\varepsilon \ne 0$ in $\Gamma_0$ the set of $\gamma$ admitting a lift $g \in \mathrm{GL}_2(K_0)$ of $\rho(\gamma)$ with all entries of valuation $\le 1$ and $v(\det g) \ge \varepsilon$ is finite. Let $a, b, z_0 \in \Omega$ with $z_0$ outside the $\rho(G)$-orbits (for the Möbius action `pmoebius`) of $a$ and of $b$. Then there exist $F, H$ in the ring $\mathrm{holRing}\ \varpi$ of functions on $\Omega$ that on each affinoid are uniform limits of uniformly bounded pole-free rational functions, forming a theta pair for $(\rho, a, b, z_0)$, i.e. $H$ is a non-zero-divisor, $H(z) = 0$ exactly on the orbit of $b$, $F(z) = 0$ exactly on the orbit of $a$, and $F(z)/H(z) = \Theta_\rho(a,b;z_0;z)$ off the orbit of $b$, and such that moreover for every $z \in \Omega$ one has $\mathrm{ordAt}\ \varpi\ F\ z = \#\{\gamma \in G : \rho(\gamma) a = z\}$ and $\mathrm{ordAt}\ \varpi\ H\ z = \#\{\gamma \in G : \rho(\gamma) b = z\}$, the cardinalities being `Nat.card` of the corresponding subtypes of $G$ and $\mathrm{ordAt}\ \varpi\ F\ z$ the supremum of the $n$ with $(\mathrm{coord} - z)^n \mid F$ in $\mathrm{holRing}\ \varpi$.
--
--   This computes the divisor of the theta function attached to a discrete subgroup of $\mathrm{PGL}_2(K_0)$ acting on Drinfeld's upper half-plane: the theta pair presenting $\Theta(a,b;z_0;\cdot)$ as a quotient of two holomorphic functions can be chosen so that its zeros are simple along each point of the two orbits, with multiplicity the number of group elements carrying $a$ (resp. $b$) to the given point. It is used in the study of orders of vanishing under the group action and in the computation of periods and of principal divisors on the associated Mumford curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_isThetaPair_ordAt_eq_card.lean

import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_isThetaPair_ordAt_eq_card
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    {a b z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀) :
    ∃ F H : ↥(holRing ϖ), IsThetaPair ϖ ρ a b z₀ F H ∧
      ∀ z : ↥(upperHalfPlane K₀ K),
        ordAt ϖ F z = Nat.card {γ : G // pmoebius K₀ (ρ γ) a = (z : K)} ∧
        ordAt ϖ H z = Nat.card {γ : G // pmoebius K₀ (ρ γ) b = (z : K)} := by sorry
