-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_monoidHom_fracAct_thetaMer_eq
-- name    : CerednikDrinfeld.Omega.exists_monoidHom_fracAct_thetaMer_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/51665e57-a085-5e64-9bb7-0a3fffaf7c8c
-- title:
--   Automorphy of the meromorphic theta function on Ω
-- statement:
--   Let $K_0$ be a field and $K$ a field that is a $K_0$-algebra, carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$ and complete for it. Let $\varpi$ be a pseudo-uniformiser: an element of $K_0$ with $0 < v(\varpi) < 1$ such that for every nonzero $a \in K_0$ some power $N$ gives $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$. Assume $\varpi$ is exhausting, i.e. every point of the Drinfeld upper half plane $\Omega = K \setminus K_0$ (the complement of the image of $K_0$) lies in one of the affinoids $\{z : v(z) \le v(\varpi)^{-n},\ v(z - a) \ge v(\varpi)^n \text{ for all } a \in K_0 \text{ with } v(a) \le v(\varpi)^{-n}\}$, and assume the ring $\mathcal{O}(\Omega)$ of functions on $\Omega$ that are uniform limits of pole-free rational functions on each affinoid, `holRing`, is a domain. Let $G$ be a group and $\rho : G \to \mathrm{PGL}_2(K_0)$ a homomorphism that is discrete in the valuative sense: for every $\varepsilon \ne 0$ in $\Gamma_0$, only finitely many $\gamma$ admit a $\mathrm{GL}_2(K_0)$-lift of $\rho(\gamma)$ with all entries of valuation $\le 1$ and determinant of valuation $\ge \varepsilon$. Let $a, b, z_0 \in \Omega$ with $\rho(\gamma)a \ne z_0$ and $\rho(\gamma)b \ne z_0$ for all $\gamma \in G$ (Möbius action via `pmoebius`). Then there is a group homomorphism $c : G \to K^\times$ such that $c(\beta) = \Theta(a,b;z_0)(\rho(\beta)z_0)$ for all $\beta$, where $\Theta(a,b;z_0)(z) = \prod'_{\gamma} [z, z_0; \rho(\gamma)a, \rho(\gamma)b]$, and such that for every $\gamma \in G$ the automorphism `Mumford.fracAct` of $\operatorname{Frac}\mathcal{O}(\Omega)$ attached to $\rho(\gamma)$ sends the meromorphic theta element `thetaMer` $\varpi\, \rho\, a\, b\, z_0$ to $c(\gamma)^{-1}$ times itself, the scalar acting through $K \to \operatorname{Frac}\mathcal{O}(\Omega)$.
--
--   This is the automorphy relation $\theta(a,b;\gamma z) = c_{a,b}(\gamma)\,\theta(a,b;z)$ of Manin–Drinfeld for theta functions of a discrete subgroup of $\mathrm{PGL}_2$, here in the form of an eigenvector statement for the induced action on the field of meromorphic functions $\operatorname{Frac}\mathcal{O}(\Omega)$, the inverse multiplier reflecting the convention $(g \cdot f)(z) = f(g^{-1}z)$. It feeds the construction of the period pairing and of divisor classes on the Mumford quotient curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_monoidHom_fracAct_thetaMer_eq.lean

import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega
open CerednikDrinfeld.Mumford

theorem CerednikDrinfeld.Omega.exists_monoidHom_fracAct_thetaMer_eq
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) [IsDomain ↥(holRing ϖ)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    {a b z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀) :
    ∃ c : G →* Kˣ,
      (∀ β : G, ((c β : Kˣ) : K) = theta ρ a b z₀ (pmoebius K₀ (ρ β) z₀)) ∧
      ∀ γ : G, Mumford.fracAct PGL(2, K₀) ↥(holRing ϖ) (ρ γ) (thetaMer ϖ ρ a b z₀) =
        algebraMap K (merField ϖ) (((c γ)⁻¹ : Kˣ) : K) * thetaMer ϖ ρ a b z₀ := by sorry
