-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_hom_comp_eq_isPullback_of_comp
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_hom_comp_eq_isPullback_of_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/6269c0f4-0b73-5062-80df-c3c242d694b7
-- title:
--   Comparison map between base changes along composable ring maps
-- statement:
--   Fix natural numbers $g,d,n$ and commutative rings $S,C,C'$ (in a fixed universe), with ring homomorphisms $\rho : S \to C$ and $\sigma : C \to C'$. Let $u,v,v'$ be polarised abelian schemes of the project's type `PolarisedAbelianScheme g d n` over $S$, $C$, $C'$ respectively; such a datum consists of a scheme $A$ with a structure morphism $f$ to the spectrum of the base ring, a commutative relative group law $L$ on the functor of points over the base, the property bundle (smooth, proper, connected fibres, a group law exists), fibres of topological Krull dimension $g$, a family $P$ of $2g$ sections over the identity which are $n$-torsion, independent and spanning the $n$-torsion of every geometric fibre, and an invertible module `pol` which is very ample in the sense of admitting a closed immersion into a relative projective space by its sections and whose geometric fibrewise $H^0$ has dimension $d$. Assume given $gv : A_v \to A_u$ making the square with $v.f$, $u.f$ and $\operatorname{Spec}\rho$ a pullback, compatible with the group laws on points (for every $T$ and every $t' : T \to \operatorname{Spec} C$ and $x,y$ over $t'$, composing $L_v$-multiplication with $gv$ agrees with $L_u$-multiplication of the composites over $t' \circ \operatorname{Spec}\rho$), carrying each level section, $(v.P\,i) \cdot gv = \operatorname{Spec}\rho$ followed by $u.P\,i$, and with $gv^{*}(u.\mathrm{pol}) \cong v.\mathrm{pol}$; and given $gv' : A_{v'} \to A_u$ satisfying the same four clauses with respect to $\sigma \circ \rho$. Then there exists $c : A_{v'} \to A_v$ with $c$ followed by $gv$ equal to $gv'$, such that the square formed by $c$, $v'.f$, $v.f$ and $\operatorname{Spec}\sigma$ is a pullback, $c$ is compatible with the group laws on points in the same sense, $(v'.P\,i)$ followed by $c$ equals $\operatorname{Spec}\sigma$ followed by $v.P\,i$ for every $i$, and $c^{*}(v.\mathrm{pol}) \cong v'.\mathrm{pol}$.
--
--   This is the transitivity of base change for polarised abelian schemes with level structure: it produces, from presentations of $v/C$ and $v'/C'$ as base changes of $u/S$ along $\rho$ and $\sigma\rho$, a morphism exhibiting $v'$ as the base change of $v$ along $\sigma$, all four clauses of the project's predicate `PolarisedAbelianScheme.IsPullback` included. It is used in the construction of charts on which the polarised abelian schemes become locally isomorphic after localisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_hom_comp_eq_isPullback_of_comp.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_hom_comp_eq_isPullback_of_comp
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
    (hgv'pol : Nonempty ((Scheme.Modules.pullback gv').obj u.pol ≅ v'.pol)) :
    ∃ (c : v'.A ⟶ v.A) (_ : c ≫ gv = gv') (hc : CategoryTheory.IsPullback c v'.f v.f (Spec.map (CommRingCat.ofHom σ))),
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of C')) (x y : SchemeHomOver t' v'.f),
        (v'.L.mul t' x y).1 ≫ c =
          (v.L.mul (t' ≫ Spec.map (CommRingCat.ofHom σ))
            ⟨x.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, y.2]⟩).1) ∧
      (∀ i, (v'.P i).1 ≫ c = Spec.map (CommRingCat.ofHom σ) ≫ (v.P i).1) ∧
      Nonempty ((Scheme.Modules.pullback c).obj v.pol ≅ v'.pol) := by sorry
