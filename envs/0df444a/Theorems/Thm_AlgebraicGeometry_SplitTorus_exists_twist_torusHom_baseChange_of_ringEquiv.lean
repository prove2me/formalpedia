-- Prove2me | Theorems.Thm_AlgebraicGeometry_SplitTorus_exists_twist_torusHom_baseChange_of_ringEquiv
-- name    : AlgebraicGeometry.SplitTorus.exists_twist_torusHom_baseChange_of_ringEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/ef122fa2-93bd-5295-9829-7ffaf76565f8
-- title:
--   Twisting torus morphisms into G×_{R_0}κ by field automorphisms
-- statement:
--   Let $R_0$ be a commutative ring, $\kappa$ a field, and $r\colon \operatorname{Spec}\kappa \to \operatorname{Spec}R_0$ a morphism of affine schemes. Let $\bar s\colon \kappa \xrightarrow{\sim}\kappa$ be a ring automorphism which is compatible with $r$ in the sense that $\operatorname{Spec}(\bar s)$ followed by $r$ equals $r$. Let $g\colon G \to \operatorname{Spec}R_0$ be a morphism of schemes equipped with a relative group law $L$, i.e. functorial multiplication, unit and inverse operations on the sets of $T$-points $\{\varphi\colon T\to G \mid \varphi \text{ over } \operatorname{Spec}R_0\}$ satisfying the group axioms; let $t$ be a natural number, and let $\tau$ be a morphism from the split torus $\operatorname{Spec}\kappa[\mathbb{Z}^t]$ (the spectrum of the additive monoid algebra of $\mathrm{Fin}\,t\to\mathbb{Z}$ over $\kappa$) to the pullback $G\times_{\operatorname{Spec}R_0}\operatorname{Spec}\kappa$, commuting with the structure morphisms to $\operatorname{Spec}\kappa$. Then there exist a self-isomorphism $\mathrm{Tw}$ of $G\times_{\operatorname{Spec}R_0}\operatorname{Spec}\kappa$ and a further morphism $\tau'$ from the split torus to this pullback over $\operatorname{Spec}\kappa$ such that: $\mathrm{Tw}$ commutes with the first projection to $G$; $\mathrm{Tw}$ followed by the second projection equals the second projection followed by $\operatorname{Spec}(\bar s^{-1})$; $\tau'$ equals $\operatorname{Spec}$ of the coefficientwise map $\bar s$ on $\kappa[\mathbb{Z}^t]$, followed by $\tau$, followed by $\mathrm{Tw}$; if $\tau$ is multiplicative on the $\kappa$-points of the torus given by the $\kappa$-algebra homomorphisms $\chi\colon \kappa[\mathbb{Z}^t]\to\kappa$ — that is, for all $\chi,\chi'$ in `WithConv` of the type of such homomorphisms, the point $\operatorname{Spec}$ of the underlying homomorphism of $\chi*\chi'$ composed with $\tau$ is the product, under the base-changed group law `L.baseChange r`, of the corresponding composites for $\chi$ and for $\chi'$ — then $\tau'$ is multiplicative in the same sense; and if $\tau$ is a closed immersion then so is $\tau'$.
--
--   This is the statement that a morphism from the split torus into the fibre $G\times_{R_0}\kappa$ may be twisted by an automorphism $\bar s$ of $\kappa$ over $R_0$, the twist preserving both multiplicativity with respect to the base-changed relative group law and the property of being a closed immersion. It is the residue-field companion of the corresponding statement over a local ring, and it is used in the analysis of the action of inertia and decomposition groups on toric lifts in the special fibres of the Néron models attached to the modular curves $X_0$ and $X_H$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SplitTorus_exists_twist_torusHom_baseChange_of_ringEquiv.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SplitTorus

theorem AlgebraicGeometry.SplitTorus.exists_twist_torusHom_baseChange_of_ringEquiv
    {R₀ : Type u} [CommRing R₀] {κ : Type u} [Field κ]
    (r : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of R₀))
    (sbar : κ ≃+* κ) (hs : Spec.map (CommRingCat.ofHom sbar.toRingHom) ≫ r = r)
    {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of R₀)) (L : RelativeGroupLaw R₀ g) (t : ℕ)
    (τ : SchemeHomOver (torusStr κ t) (RelativeGroupLaw.baseChangeStr r g)) :
    ∃ (Tw : pullback g r ≅ pullback g r) (τ' : SchemeHomOver (torusStr κ t) (RelativeGroupLaw.baseChangeStr r g)),

      Tw.hom ≫ pullback.fst g r = pullback.fst g r ∧
      Tw.hom ≫ pullback.snd g r = pullback.snd g r ≫ Spec.map (CommRingCat.ofHom sbar.symm.toRingHom) ∧

      τ'.1 = Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin t → ℤ) sbar.toRingHom)) ≫ τ.1 ≫ Tw.hom ∧

      ((∀ χ χ' : WithConv (torusCoord κ t →ₐ[κ] κ),
          NeronModelInfra.schemeHomOverComp (torusPtId κ t (χ * χ').ofConv) τ =
            (L.baseChange r).mul _ (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ.ofConv) τ)
              (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ'.ofConv) τ)) →
        ∀ χ χ' : WithConv (torusCoord κ t →ₐ[κ] κ),
          NeronModelInfra.schemeHomOverComp (torusPtId κ t (χ * χ').ofConv) τ' =
            (L.baseChange r).mul _ (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ.ofConv) τ')
              (NeronModelInfra.schemeHomOverComp (torusPtId κ t χ'.ofConv) τ')) ∧

      (IsClosedImmersion τ.1 → IsClosedImmersion τ'.1) := by sorry
