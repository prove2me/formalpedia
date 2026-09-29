-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_iso_of_isPullback_of_isPullback
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.iso_of_isPullback_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/1e12dad0-e8a2-57cd-9027-3b4fe356e13e
-- title:
--   Uniqueness of base change for QM structures
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, a map $star\colon\Lambda\to\Lambda$, a family $\beta\colon \mathrm{Fin}(2\cdot 2)\to\Lambda$, natural numbers $d,m$, commutative rings $S,S'$ and a ring homomorphism $\varphi\colon S\to S'$. Let $X$ be a polarised abelian scheme of relative fibre dimension $2$ with invariants $d,m$ over $S$, let $X_1,X_2$ be such over $S'$, and let $t,t_1,t_2$ be $\mathrm{QMStructure}\ \Lambda\ star\ \beta$ structures on $X,X_1,X_2$ respectively. Assume $\mathrm{QMStructure.IsPullback}\ \varphi\ t\ t_i$ for $i=1,2$, i.e. for each $i$ there are a morphism $g_i\colon X_i.A\to X.A$ making the square with $X_i.f$, $X.f$ and $\mathrm{Spec}\,\varphi$ cartesian, such that $g_i$ carries the group law on points over $S'$-schemes to that over $S$, carries each level section $X_i.P\,j$ to $\mathrm{Spec}\,\varphi$ followed by $X.P\,j$, the $g_i$-pullback of $X.\mathrm{pol}$ is isomorphic to $X_i.\mathrm{pol}$, $g_i$ intertwines the $\Lambda$-actions ($t_i.\mathrm{act}\,x$ followed by $g_i$ equals $g_i$ followed by $t.\mathrm{act}\,x$), and $t_i.P$ followed by $g_i$ equals $\mathrm{Spec}\,\varphi$ followed by $t.P$. The conclusion is $\mathrm{QMStructure.Iso}\ t_1\ t_2$: an isomorphism $e\colon X_1.A\cong X_2.A$ over $S'$ compatible with the group laws on points, with the level sections, with the $\Lambda$-actions, sending $t_1.P$ to $t_2.P$, and identifying the $e$-pullback of $X_2.\mathrm{pol}$ with $X_1.\mathrm{pol}$ after restriction over some open neighbourhood of each point of $\mathrm{Spec}\,S'$.
--
--   This is the uniqueness-up-to-isomorphism of the base change of a polarised abelian surface with quaternionic multiplication and level data along a ring homomorphism, the bookkeeping that makes the associated moduli problem a well-defined functor. It is used in the construction and comparison of points of the fake elliptic curve moduli problem, notably in the statements about exhibiting points over affine charts and about comparing two such points after base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_iso_of_isPullback_of_isPullback_1.lean

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.iso_of_isPullback_of_isPullback
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ} {β : Fin (2 * 2) → ↥Λ} {d m : ℕ}
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    {X : PolarisedAbelianScheme 2 d m S} {X₁ X₂ : PolarisedAbelianScheme 2 d m S'}
    {t : QMStructure Λ star β X} {t₁ : QMStructure Λ star β X₁} {t₂ : QMStructure Λ star β X₂}
    (h₁ : QMStructure.IsPullback φ t t₁) (h₂ : QMStructure.IsPullback φ t t₂) :
    QMStructure.Iso t₁ t₂ := by sorry
