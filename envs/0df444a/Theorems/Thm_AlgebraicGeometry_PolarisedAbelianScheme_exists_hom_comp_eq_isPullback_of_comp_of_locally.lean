-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_hom_comp_eq_isPullback_of_comp_of_locally
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_hom_comp_eq_isPullback_of_comp_of_locally
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/02549afd-e2db-5228-a219-6c2bc5dbd74b
-- title:
--   Comparison map of two base changes, polarisation locally
-- statement:
--   Fix naturals $g,d,n$ and commutative rings $S,C,C'$ with ring homomorphisms $\rho : S \to C$ and $\sigma : C \to C'$, and let $u,v,v'$ be polarised abelian schemes of type $(g,d,n)$ over $S$, $C$, $C'$ respectively, each consisting of a scheme over the spectrum of its base ring together with a commutative relative group law, an abelian-scheme property bundle, $g$-dimensional fibres, $2g$ independent spanning $n$-torsion sections $P_i$, and an invertible, very ample module `pol` of geometric fibre rank $d$. Assume given $gv : v.A \to u.A$ making the square with $v.f$, $u.f$ and $\operatorname{Spec}\rho$ cartesian, compatible with the group laws on points (for every $T \to \operatorname{Spec} C$ and every pair of $T$-points of $v$ over it, the product composed with $gv$ is the product of the composites), carrying $P_i^{v}$ to $P_i^{u}$ base changed along $\operatorname{Spec}\rho$, and with a global isomorphism $gv^{*}u.\mathrm{pol} \cong v.\mathrm{pol}$; and likewise $gv' : v'.A \to u.A$ cartesian over $\operatorname{Spec}(\sigma\circ\rho)$, multiplicative on points and carrying the level sections, but with the polarisation clause only locally on the base: every point $s$ of $\operatorname{Spec} C'$ has an open neighbourhood $U$ such that $gv'^{*}u.\mathrm{pol}$ and $v'.\mathrm{pol}$ become isomorphic after restriction to the open subscheme $v'.f^{-1}U$ of $v'.A$. Then there exists $c : v'.A \to v.A$ with $c$ followed by $gv$ equal to $gv'$, such that the square formed by $c$, $v'.f$, $v.f$ and $\operatorname{Spec}\sigma$ is cartesian, $c$ is multiplicative on points, $c$ carries each $P_i^{v'}$ to $\operatorname{Spec}\sigma$ followed by $P_i^{v}$, and the polarisation clause holds locally: every $s \in \operatorname{Spec} C'$ has an open neighbourhood $U$ with $c^{*}v.\mathrm{pol}$ and $v'.\mathrm{pol}$ isomorphic after restriction to $v'.f^{-1}U$.
--
--   This is the transitivity (cancellation) step for base change of polarised abelian schemes: from presentations of $v/C$ and $v'/C'$ as base changes of $u/S$ along $\rho$ and $\sigma\rho$ it produces the comparison morphism exhibiting $v'$ as the base change of $v$ along $\sigma$, in the variant where the comparison of polarisations is only required locally on the base. It is used in the construction of charts on which the polarised abelian schemes become locally isomorphic after base change to localisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_hom_comp_eq_isPullback_of_comp_of_locally.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_hom_comp_eq_isPullback_of_comp_of_locally
    {g d n : ℕ} {S C C' : Type u} [CommRing S] [CommRing C] [CommRing C'] (ρ : S →+* C) (σ : C →+* C')
    (u : PolarisedAbelianScheme g d n S) (v : PolarisedAbelianScheme g d n C) (v' : PolarisedAbelianScheme g d n C')
    (gv : v.A ⟶ u.A) (hgv : CategoryTheory.IsPullback gv v.f u.f (Spec.map (CommRingCat.ofHom ρ)))
    (hgvmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of C)) (x y : SchemeHomOver t' v.f),
      (v.L.mul t' x y).1 ≫ gv =
        (u.L.mul (t' ≫ Spec.map (CommRingCat.ofHom ρ))
          ⟨x.1 ≫ gv, by rw [Category.assoc, hgv.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gv, by rw [Category.assoc, hgv.w, ← Category.assoc, y.2]⟩).1)
    (hgvP : ∀ i, (v.P i).1 ≫ gv = Spec.map (CommRingCat.ofHom ρ) ≫ (u.P i).1)
    (hgvpol : Nonempty ((Scheme.Modules.pullback gv).obj u.pol ≅ v.pol))
    (gv' : v'.A ⟶ u.A) (hgv' : CategoryTheory.IsPullback gv' v'.f u.f (Spec.map (CommRingCat.ofHom (σ.comp ρ))))
    (hgv'mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of C')) (x y : SchemeHomOver t' v'.f),
      (v'.L.mul t' x y).1 ≫ gv' =
        (u.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (σ.comp ρ)))
          ⟨x.1 ≫ gv', by rw [Category.assoc, hgv'.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gv', by rw [Category.assoc, hgv'.w, ← Category.assoc, y.2]⟩).1)
    (hgv'P : ∀ i, (v'.P i).1 ≫ gv' = Spec.map (CommRingCat.ofHom (σ.comp ρ)) ≫ (u.P i).1)
    (hgv'pol : ∀ s : ↥(Spec (CommRingCat.of C')), ∃ U : (Spec (CommRingCat.of C')).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (v'.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback gv').obj u.pol) ≅
        (Scheme.Modules.pullback (v'.f ⁻¹ᵁ U).ι).obj v'.pol)) :
    ∃ (c : v'.A ⟶ v.A) (_ : c ≫ gv = gv') (hc : CategoryTheory.IsPullback c v'.f v.f (Spec.map (CommRingCat.ofHom σ))),
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of C')) (x y : SchemeHomOver t' v'.f),
        (v'.L.mul t' x y).1 ≫ c =
          (v.L.mul (t' ≫ Spec.map (CommRingCat.ofHom σ))
            ⟨x.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, y.2]⟩).1) ∧
      (∀ i, (v'.P i).1 ≫ c = Spec.map (CommRingCat.ofHom σ) ≫ (v.P i).1) ∧
      (∀ s : ↥(Spec (CommRingCat.of C')), ∃ U : (Spec (CommRingCat.of C')).Opens, s ∈ U ∧
        Nonempty ((Scheme.Modules.pullback (v'.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback c).obj v.pol) ≅
          (Scheme.Modules.pullback (v'.f ⁻¹ᵁ U).ι).obj v'.pol)) := by sorry
