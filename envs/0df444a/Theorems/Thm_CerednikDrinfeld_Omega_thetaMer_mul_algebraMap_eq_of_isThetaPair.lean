-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_thetaMer_mul_algebraMap_eq_of_isThetaPair
-- name    : CerednikDrinfeld.Omega.thetaMer_mul_algebraMap_eq_of_isThetaPair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/36cf198e-7cb5-59df-af80-e0c68cafb8fa
-- title:
--   Defining relation thetaMer· H = F for a theta pair
-- statement:
--   Let $K_0$ and $K$ be fields with $K$ a $K_0$-algebra, $K$ equipped with decidable equality and with a valuation taking values in a linearly ordered commutative group with zero $\Gamma_0$. Let $\varpi$ be a `PseudoUniformizer` for $K_0$ in $K$, i.e. an element of $K_0$ whose image in $K$ has valuation strictly between $0$ and $1$ and such that for every nonzero $a \in K_0$ the valuation of the image of $a$ lies between $v(\varpi)^N$ and $v(\varpi)^{-N}$ for some $N \in \mathbb{N}$. Let $G$ be a group, $\rho : G \to \mathrm{PGL}(2,K_0)$ a homomorphism, and $a, b, z_0 \in K$. Let $F, H$ belong to `holRing` $\varpi$, the subring of functions on Drinfeld's upper half plane $\Omega = K \setminus \mathrm{image}(K_0 \to K)$ whose restriction to each affinoid $\varpi$-level set is a uniform limit of a uniformly bounded sequence of rational functions without poles there. Assume `IsThetaPair` $\varpi\,\rho\,a\,b\,z_0\,F\,H$, that is: $H$ is a non-zero-divisor of `holRing` $\varpi$; for $z \in \Omega$, $H(z) = 0$ exactly when $z$ lies in the $\rho(G)$-orbit of $b$ under the projective Möbius action `pmoebius`; $F(z) = 0$ exactly when $z$ lies in the $\rho(G)$-orbit of $a$; and for every $z \in \Omega$ outside the orbit of $b$, $F(z)/H(z)$ equals $\mathrm{theta}\,\rho\,a\,b\,z_0\,z$, the infinite product over $G$ of the theta factors. The conclusion is that in `merField` $\varpi$, the fraction field of `holRing` $\varpi$, the element `thetaMer` $\varpi\,\rho\,a\,b\,z_0$ — defined as the class of a chosen theta pair when one exists and as $0$ otherwise — multiplied by the image of $H$ under the structure map equals the image of $F$.
--
--   This is the defining relation of the theta function of the discrete group $\rho(G)$ viewed as a meromorphic function on Drinfeld's upper half plane: it identifies `thetaMer` with the fraction $F/H$ for an arbitrary theta pair $(F,H)$, and thereby makes the choice made in the definition of `thetaMer` invisible. It is the form in which later results read off the zeros of $\Theta$ along the orbit of $a$ and its poles along the orbit of $b$, and transport $\Theta$ under the Möbius and coefficientwise actions; it is cited by the transfer and equivariance statements for `thetaMer`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_thetaMer_mul_algebraMap_eq_of_isThetaPair.lean

import Definitions.Def_CerednikDrinfeld_ThetaMer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.thetaMer_mul_algebraMap_eq_of_isThetaPair
    {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (a b z₀ : K)
    (F H : ↥(holRing ϖ)) (h : IsThetaPair ϖ ρ a b z₀ F H) :
    thetaMer ϖ ρ a b z₀ * algebraMap ↥(holRing ϖ) (merField ϖ) H = algebraMap ↥(holRing ϖ) (merField ϖ) F := by sorry
