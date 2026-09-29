-- Prove2me | Theorems.Thm_AlgebraicGeometry_SplitTorus_exists_addEquiv_eq_specMap_mapDomain_comp_of_range_eq
-- name    : AlgebraicGeometry.SplitTorus.exists_addEquiv_eq_specMap_mapDomain_comp_of_range_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/2baef28f-578b-53d8-91ca-a13a1a8330bf
-- title:
--   Rigidity of closed split sub-tori up to GLₜ(ℤ)
-- statement:
--   Let $\kappa$ be an algebraically closed field, let $f \colon Y \to \operatorname{Spec}\kappa$ be a separated morphism of schemes, and let $L$ be a relative group law on $f$: a rule assigning to every $\kappa$-scheme $t \colon T \to \operatorname{Spec}\kappa$ a multiplication, unit and inversion on the set of morphisms $T \to Y$ over $\operatorname{Spec}\kappa$, satisfying associativity, the two unit laws and left inversion, and natural in $T$ under precomposition. Fix $t \in \mathbb{N}$ and write the split torus as $\operatorname{Spec}$ of the group algebra $\kappa[\mathbb{Z}^t]$, $\mathbb{Z}^t = (\mathrm{Fin}\,t \to \mathbb{Z})$, with its structure morphism to $\operatorname{Spec}\kappa$. Let $\tau, \tau'$ be morphisms from this torus to $Y$ over $\operatorname{Spec}\kappa$, both closed immersions on the underlying morphisms of schemes. Assume each of $\tau$ and $\tau'$ is multiplicative on $\kappa$-points, in the following sense: for all $\kappa$-algebra homomorphisms $\chi, \chi' \colon \kappa[\mathbb{Z}^t] \to \kappa$, viewed in the type `WithConv` carrying the convolution product, the $\kappa$-point of $Y$ obtained by composing $\operatorname{Spec}$ of $\chi\chi'$ with the morphism in question equals the $L$-product of the $\kappa$-points obtained from $\chi$ and from $\chi'$. Assume finally that $\tau$ and $\tau'$ have the same set-theoretic image in $Y$. Then there is an automorphism $M$ of the additive group $\mathbb{Z}^t$ such that $\tau'$ equals $\operatorname{Spec}$ of the ring homomorphism $\kappa[\mathbb{Z}^t] \to \kappa[\mathbb{Z}^t]$ induced by $M$ on the grading group, followed by $\tau$.
--
--   This is the rigidity statement that a closed split subtorus of a separated group scheme over an algebraically closed field is determined by its support up to the action of $\mathrm{GL}_t(\mathbb{Z})$ on the character lattice. It is used in the analysis of the toric part of the Néron model of the Jacobian of a modular curve at a prime of bad reduction, where it supplies the uniqueness, up to $\mathrm{GL}_t(\mathbb{Z})$, of a toric lift of a given torus fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SplitTorus_exists_addEquiv_eq_specMap_mapDomain_comp_of_range_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SplitTorus

theorem AlgebraicGeometry.SplitTorus.exists_addEquiv_eq_specMap_mapDomain_comp_of_range_eq
    {κ : Type} [Field κ] [IsAlgClosed κ]
    {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of κ)) [IsSeparated f] (L : RelativeGroupLaw κ f) (t : ℕ)
    (τ τ' : SchemeHomOver (torusStr κ t) f) (hτ : IsClosedImmersion τ.1) (hτ' : IsClosedImmersion τ'.1)
    (hτmul : ∀ χ χ' : WithConv (torusCoord κ t →ₐ[κ] κ),
      NeronModelInfra.schemeHomOverComp (torusPtId κ t (χ * χ').ofConv) τ =
        L.mul _ (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ.ofConv) τ)
          (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ'.ofConv) τ))
    (hτ'mul : ∀ χ χ' : WithConv (torusCoord κ t →ₐ[κ] κ),
      NeronModelInfra.schemeHomOverComp (torusPtId κ t (χ * χ').ofConv) τ' =
        L.mul _ (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ.ofConv) τ')
          (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ'.ofConv) τ'))
    (hrange : Set.range τ'.1.base = Set.range τ.1.base) :
    ∃ Mx : (Fin t → ℤ) ≃+ (Fin t → ℤ),
      τ'.1 = Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ (Mx : (Fin t → ℤ) →+ (Fin t → ℤ)))) ≫ τ.1 := by sorry
