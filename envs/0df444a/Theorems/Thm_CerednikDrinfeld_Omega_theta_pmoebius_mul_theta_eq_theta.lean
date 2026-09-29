-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_theta_pmoebius_mul_theta_eq_theta
-- name    : CerednikDrinfeld.Omega.theta_pmoebius_mul_theta_eq_theta
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/905c4db5-50be-5766-a523-a14462c6491e
-- title:
--   Theta multiplier as a ratio of theta units
-- statement:
--   Let $K_0 \subseteq K$ be fields with $K$ a $K_0$-algebra carrying a Hausdorff topological ring structure, and let $\rho : G \to \mathrm{PGL}(2,K_0)$ be a homomorphism from a group $G$. For $g \in \mathrm{PGL}(2,K_0)$ and $z \in K$ write $\mathrm{pmoebius}\,g\,z$ for the image of $z$ under the action of $g$ on $\mathbb{P}^1(K) = \mathrm{OnePoint}\,K$, read back in $K$ with $\infty$ sent to $0$, and for $x,y,p,q \in K$ put $\mathrm{theta}\,\rho\,x\,y\,p\,q = {\prod}'_{\gamma \in G} \mathrm{crossRatio}\,q\,p\,(\mathrm{pmoebius}(\rho\gamma)x)\,(\mathrm{pmoebius}(\rho\gamma)y)$, the unconditional product of the cross-ratio factors. Assume $a, b, z_0, w$ lie in $\mathrm{upperHalfPlane}\,K_0\,K$, the complement in $K$ of the image of the structure map $K_0 \to K$; assume $\mathrm{pmoebius}(\rho\gamma)a \neq z_0$, $\mathrm{pmoebius}(\rho\gamma)b \neq z_0$ and $\mathrm{pmoebius}(\rho\gamma)z_0 \neq w$ for every $\gamma \in G$. Let $\beta \in G$ and set $z_\beta = \mathrm{pmoebius}(\rho\beta)z_0$. If the families of cross-ratio factors defining $\mathrm{theta}\,\rho\,a\,b\,z_0\,z_\beta$ and $\mathrm{theta}\,\rho\,z_0\,z_\beta\,w\,a$ are multipliable, then $$\mathrm{theta}\,\rho\,a\,b\,z_0\,z_\beta \cdot \mathrm{theta}\,\rho\,z_0\,z_\beta\,w\,a = \mathrm{theta}\,\rho\,z_0\,z_\beta\,w\,b.$$ No multipliability hypothesis is imposed on the right-hand product.
--
--   This is the dictionary between the automorphy factor of the theta product attached to the pair $(a,b)$, namely its value at $\mathrm{pmoebius}(\rho\beta)z_0$, and the quotient of the values at $b$ and at $a$ of the theta unit attached to $\beta$; in the classical Schottky-group setting it is the relation $c_{a,b}(\beta) = u_\beta(b)/u_\beta(a)$. It is used in the construction of the multiplicative period pairing on $\Omega$, in the statements producing points and pairs with prescribed valuations of products of theta functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_theta_pmoebius_mul_theta_eq_theta.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.theta_pmoebius_mul_theta_eq_theta
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a b z₀ w : K}
    (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hw : w ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀)
    (hwz₀ : ∀ γ : G, pmoebius K₀ (ρ γ) z₀ ≠ w) (β : G)
    (h₁ : ThetaMultipliable ρ a b z₀ (pmoebius K₀ (ρ β) z₀))
    (h₂ : ThetaMultipliable ρ z₀ (pmoebius K₀ (ρ β) z₀) w a) :
    theta ρ a b z₀ (pmoebius K₀ (ρ β) z₀) * theta ρ z₀ (pmoebius K₀ (ρ β) z₀) w a =
      theta ρ z₀ (pmoebius K₀ (ρ β) z₀) w b := by sorry
