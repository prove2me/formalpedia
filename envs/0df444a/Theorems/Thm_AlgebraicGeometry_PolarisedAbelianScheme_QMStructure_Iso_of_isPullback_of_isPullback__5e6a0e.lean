-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_Iso_of_isPullback_of_isPullback__5e6a0e
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.Iso.of_isPullback_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/5e6a0eb6-8878-5ec2-8b1d-096550f8576d
-- title:
--   Base change of a QM isomorphism along φ
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a map $star\colon \Lambda \to \Lambda$, a family $\beta\colon \mathrm{Fin}\,4 \to \Lambda$ and naturals $d,m$; let $\varphi\colon S \to S'$ be a homomorphism of commutative rings, let $X_1,X_2$ be polarised abelian schemes of relative dimension $2$, geometric fibre $H^0$-rank $d$ and $m$-torsion basis over $S$, let $X_1',X_2'$ be such data over $S'$, and let $t_1,t_2,t_1',t_2'$ be $\mathrm{QMStructure}$s for $(\Lambda,star,\beta)$ on $X_1,X_2,X_1',X_2'$ respectively. Assume: (i) $\mathrm{QMStructure.Iso}\ t_1\ t_2$, i.e. there is an isomorphism $e\colon X_1.A \cong X_2.A$ over $S$ whose forward map is multiplicative for the relative group laws on points over any base, carries each marked torsion section $X_1.P\,i$ to $X_2.P\,i$, pulls the polarisation $X_2.\mathrm{pol}$ back to $X_1.\mathrm{pol}$ locally over the base (on preimages of a neighbourhood of each point of $\operatorname{Spec} S$), intertwines the two $\Lambda$-actions, and carries $t_1.P$ to $t_2.P$; (ii) for $i=1,2$, $\mathrm{QMStructure.IsPullback}\ \varphi\ t_i\ t_i'$, i.e. there is $g_i\colon X_i'.A \to X_i.A$ making a cartesian square with the structure morphisms and $\operatorname{Spec}\varphi$, compatible with the group laws, with the marked torsion sections, with the polarisations (the pullback of $X_i.\mathrm{pol}$ along $g_i$ is isomorphic to $X_i'.\mathrm{pol}$), with the $\Lambda$-actions, and with $t_i.P$. The conclusion is $\mathrm{QMStructure.Iso}\ t_1'\ t_2'$.
--
--   This is the base-change invariance of the isomorphism relation in the moduli problem of quaternionic multiplication (fake elliptic curve) data on polarised abelian surfaces: isomorphic objects over $S$ have isomorphic base changes over $S'$. It is used in the construction and comparison of affine charts for the quaternionic moduli problem, in particular in the results producing transition data between charts and identifying marked sections across charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_Iso_of_isPullback_of_isPullback.lean

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.Iso.of_isPullback_of_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ} {β : Fin (2 * 2) → ↥Λ} {d m : ℕ}
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    {X₁ X₂ : PolarisedAbelianScheme 2 d m S} {X₁' X₂' : PolarisedAbelianScheme 2 d m S'}
    {t₁ : QMStructure Λ star β X₁} {t₂ : QMStructure Λ star β X₂}
    {t₁' : QMStructure Λ star β X₁'} {t₂' : QMStructure Λ star β X₂'}
    (h : QMStructure.Iso t₁ t₂) (h₁ : QMStructure.IsPullback φ t₁ t₁') (h₂ : QMStructure.IsPullback φ t₂ t₂') :
    QMStructure.Iso t₁' t₂' := by sorry
