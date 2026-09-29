-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCanonicalPolData_of_locIsoOnBase
-- name    : CerednikDrinfeld.QM.IsCanonicalPolData.of_locIsoOnBase
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/0bf6a866-69b0-5a7c-af13-bee3ed43c8e4
-- title:
--   Canonical polarisation data transfer along base-local isomorphisms
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme, $f : A \to \operatorname{Spec} S$ a morphism and $L$ a relative group law on $f$ (functorial multiplication, unit and inverse on $T$-points over $\operatorname{Spec} S$, with associativity, unit and inverse laws and naturality in $T$). Let $I$ be an index type, $\mathrm{act} : I \to (A \to A)$ a family of endomorphisms with $\mathrm{act}\,x$ followed by $f$ equal to $f$ for each $x$, and $\mathrm{star} : I \to I$. Let $\mathcal L, \mathcal L'$ be modules on $A$, assume $\mathcal L'$ is invertible (locally on $A$ its restriction is isomorphic to the unit module), and assume `LocIsoOnBase f 𝓛 𝓛'`: every point $s$ of $\operatorname{Spec} S$ has an open neighbourhood $U$ such that the restrictions of $\mathcal L$ and $\mathcal L'$ to $f^{-1}U$ are isomorphic. If $\mathcal L$ is canonical polarisation data for $(f, L, \mathrm{act}, \mathrm{star})$, then so is $\mathcal L'$; that is, $\mathcal L'$ is invertible, is symmetric (its pullback along the inversion morphism is base-locally isomorphic to it), the vanishing locus of its Mumford bundle on slices is exactly the $2$-torsion, there is a faithfully flat $S$-algebra $S'$ over which, for every relative group law $L'$ on the base change compatible with $L$ along the first projection, the pullback of $\mathcal L'$ is base-locally isomorphic to $\mathcal L_0 \otimes [-1]^*\mathcal L_0$ for some invertible $\mathcal L_0$ with trivial kernel, all geometric fibres over algebraically closed fields have positive $H^0$-rank, and the Rosati compatibility with $\mathrm{act}$ and $\mathrm{star}$ holds.
--
--   This is the invariance of the canonical polarisation data condition under replacing the invertible module by one isomorphic to it locally over the base, the relation used in this development in place of equality in the relative Picard group. It is invoked when the canonical polarisation on a fake elliptic curve is transported along base changes, localisations and isomorphisms of the underlying abelian scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCanonicalPolData_of_locIsoOnBase.lean

import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

universe u v

theorem CerednikDrinfeld.QM.IsCanonicalPolData.of_locIsoOnBase
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {I : Type v} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f) (star : I → I)
    (𝓛 𝓛' : A.Modules) (h𝓛' : Scheme.Modules.IsInvertible 𝓛') (h : LocIsoOnBase f 𝓛 𝓛')
    (h𝓛 : CerednikDrinfeld.QM.IsCanonicalPolData f L act act_over star 𝓛) :
    CerednikDrinfeld.QM.IsCanonicalPolData f L act act_over star 𝓛' := by sorry
