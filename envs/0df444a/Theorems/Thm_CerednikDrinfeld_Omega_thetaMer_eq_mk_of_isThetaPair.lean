-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_thetaMer_eq_mk_of_isThetaPair
-- name    : CerednikDrinfeld.Omega.thetaMer_eq_mk_of_isThetaPair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/631933e5-b001-5031-9caa-5d24d782e180
-- title:
--   Any theta pair presents `thetaMer`
-- statement:
--   Let $K_0$ be a field, $K$ a field with a $K_0$-algebra structure and a valuation with values in a linearly ordered commutative group with zero $\Gamma_0$, and let $\varpi$ be a pseudo-uniformizer of $K_0$ in $K$ (an element of $K_0$ whose value in $K$ lies strictly between $0$ and $1$ and such that every non-zero element of $K_0$ has value between $\mathfrak p^N$ and $\mathfrak p^{-N}$ for some $N$, where $\mathfrak p$ is the value of $\varpi$). Let $G$ be a group, $\rho : G \to \mathrm{PGL}(2,K_0)$ a group homomorphism, and $a,b,z_0 \in K$. Let $F,H$ be elements of `holRing` $\varpi$, the subring of those functions on the Drinfeld upper half plane $\Omega = K \setminus \operatorname{im}(K_0 \to K)$ whose restriction to each affinoid `affinoid` $\varpi\, n$ is a uniform limit of a uniformly bounded sequence of rational functions without poles there. Assume `IsThetaPair` $\varpi\,\rho\,a\,b\,z_0\,F\,H$, that is: $H$ is a non-zero-divisor in `holRing` $\varpi$; $H(z) = 0$ exactly for those $z \in \Omega$ in the $\rho(G)$-orbit of $b$ under the projective Möbius action `pmoebius`; $F(z) = 0$ exactly on the corresponding orbit of $a$; and $F(z)/H(z) =$ `theta` $\rho\,a\,b\,z_0\,z$ for every $z \in \Omega$ off the orbit of $b$. Then `thetaMer` $\varpi\,\rho\,a\,b\,z_0$, defined by choosing some theta pair if one exists and $0$ otherwise, equals the fraction $F/H$ in `merField` $\varpi = \operatorname{Frac}(\,$`holRing` $\varpi)$.
--
--   This is the independence-of-presentation statement for the meromorphic theta function attached to $\rho$ on Drinfeld's upper half plane: the choice made in the definition of `thetaMer` is immaterial, so any explicitly constructed theta pair computes it. It is used wherever theta functions are exhibited concretely, for instance in the results on periods and on principal divisors of differences of orbit sums on the associated curve, and in the construction of invariant functions vanishing at prescribed points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_thetaMer_eq_mk_of_isThetaPair.lean

import Definitions.Def_CerednikDrinfeld_ThetaMer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.thetaMer_eq_mk_of_isThetaPair
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (a b z₀ : K)
    (F H : ↥(holRing ϖ)) (h : IsThetaPair ϖ ρ a b z₀ F H) :
    thetaMer ϖ ρ a b z₀ = Localization.mk F ⟨H, h.1⟩ := by sorry
