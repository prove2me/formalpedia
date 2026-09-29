-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_period_eq_period_of_mem_upperHalfPlane
-- name    : CerednikDrinfeld.Omega.period_eq_period_of_mem_upperHalfPlane
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/b66a1212-cfef-50f9-8159-473e72796173
-- title:
--   Periods are independent of the auxiliary point a
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra which is itself a field, carrying a topology making it a Hausdorff topological ring, and let $\Omega = K \setminus \mathrm{image}(K_0 \to K)$ be the set `upperHalfPlane K₀ K`, the complement of the image of the structure map. Let $G$ be a group and $\rho \colon G \to \mathrm{PGL}_2(K_0)$ a homomorphism, acting on points of $K$ by `pmoebius`, the Möbius action on $\mathbb{P}^1(K) =$ `OnePoint K` followed by the map sending $\infty$ to $0$ and fixing affine points. Let $a, a', z_0 \in \Omega$, and assume no $\rho$-translate $\rho(\gamma) a$ or $\rho(\gamma) a'$ ($\gamma \in G$) equals $z_0$. Assume further that for all $x, y, z \in \Omega$ the family $\gamma \mapsto [z, z_0; \rho(\gamma) x, \rho(\gamma) y]$ of cross-ratios is multipliable, so that $\Theta(x,y;z_0;z) = \prod'_{\gamma \in G} [z,z_0;\rho(\gamma)x,\rho(\gamma)y]$, the value of `theta`, is given by an unconditionally convergent product. Then for all $\alpha, \beta \in G$ the periods agree: $$\Theta\bigl(a, \rho(\alpha)a; z_0; \rho(\beta)z_0\bigr) = \Theta\bigl(a', \rho(\alpha)a'; z_0; \rho(\beta)z_0\bigr),$$ i.e. `period ρ a z₀ α β = period ρ a' z₀ α β`.
--
--   This is the independence of the Manin–Drinfeld period pairing $Q(\alpha,\beta) = \Theta(a,\alpha a; z_0; \beta z_0)$ attached to a Schottky-type group acting on the Drinfeld upper half plane from the choice of auxiliary divisor point $a$. It is used in establishing the symmetry of the period pairing and in the construction of the period datum attached to a Mumford quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_period_eq_period_of_mem_upperHalfPlane.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.period_eq_period_of_mem_upperHalfPlane
    {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) {a a' z₀ : K}
    (ha : a ∈ upperHalfPlane K₀ K) (ha' : a' ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀a' : ∀ γ : G, pmoebius K₀ (ρ γ) a' ≠ z₀)
    (hΘ : ∀ x ∈ upperHalfPlane K₀ K, ∀ y ∈ upperHalfPlane K₀ K, ∀ z ∈ upperHalfPlane K₀ K,
      ThetaMultipliable ρ x y z₀ z)
    (α β : G) :
    period ρ a z₀ α β = period ρ a' z₀ α β := by sorry
