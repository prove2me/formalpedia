-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_schemeHomOver_comp_eq_comp_of_isPullback
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_schemeHomOver_comp_eq_comp_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/24be664a-9efa-51e6-9d75-708cae1c5f2f
-- title:
--   Automorphisms descend along a cartesian comparison map
-- statement:
--   Fix natural numbers $g,d,n$, commutative rings $S,S'$ and a ring homomorphism $\varphi : S \to S'$, and let $u$, $u'$ be data of type `PolarisedAbelianScheme g d n` over $S$ and over $S'$ respectively, with structure morphisms $u.f : u.A \to \operatorname{Spec} S$, $u'.f : u'.A \to \operatorname{Spec} S'$, relative group laws $u.L$, $u'.L$ and invertible modules $u.\mathrm{pol}$, $u'.\mathrm{pol}$. Assume given $g_A : u'.A \to u.A$ making the square with $u'.f$, $u.f$ and $\operatorname{Spec}\varphi$ cartesian, such that $g_A$ is multiplicative on points (for every scheme $T$, every $t' : T \to \operatorname{Spec} S'$ and all $x,y \in \mathrm{SchemeHomOver}\,t'\,u'.f$, the product $u'.L.\mathrm{mul}\,t'\,x\,y$ followed by $g_A$ is the $u.L$-product over $t'$ followed by $\operatorname{Spec}\varphi$ of $x$ followed by $g_A$ and $y$ followed by $g_A$), and such that $(g_A)^{*}u.\mathrm{pol} \cong u'.\mathrm{pol}$; these are the clauses of `PolarisedAbelianScheme.IsPullback` apart from the one on the level-$n$ points. Assume further $\sigma : u.A \to u.A$ with $\sigma \circ u.f$-compatibility $\sigma \gg u.f = u.f$, with $\sigma$ an isomorphism, multiplicative on $T$-points for every $T$ and every $t : T \to \operatorname{Spec} S$, and such that each point $s$ of $\operatorname{Spec} S$ has an open neighbourhood $U$ for which $\sigma^{*}u.\mathrm{pol}$ and $u.\mathrm{pol}$ become isomorphic after pullback along the inclusion of $u.f^{-1}U$. The conclusion is the existence of $\sigma' : u'.A \to u'.A$ over $\operatorname{Spec} S'$ which is an isomorphism, is multiplicative on points over every $t : T \to \operatorname{Spec} S'$, satisfies the same local preservation of $u'.\mathrm{pol}$ over opens of $\operatorname{Spec} S'$, and is compatible with $\sigma$ in the sense that $\sigma'$ followed by $g_A$ equals $g_A$ followed by $\sigma$.
--
--   This is the base-change step for automorphisms of a polarised abelian scheme: an automorphism of the total space over $S$ which respects the group law and, locally on the base, the polarisation, is carried along a cartesian comparison map to such an automorphism over $S'$. It is used in the passage from a general base to a field in the proof that such automorphisms have bounded order, in the spirit of Mumford's theorem on automorphisms fixing a polarisation and the level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_schemeHomOver_comp_eq_comp_of_isPullback.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_schemeHomOver_comp_eq_comp_of_isPullback
    {g d n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S')
    (gA : u'.A ⟶ u.A) (hg : CategoryTheory.IsPullback gA u'.f u.f (Spec.map (CommRingCat.ofHom φ)))
    (hgmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' u'.f),
      (u'.L.mul t' x y).1 ≫ gA =
        (u.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    (hgpol : Nonempty ((Scheme.Modules.pullback gA).obj u.pol ≅ u'.pol))
    (σ : SchemeHomOver u.f u.f) (hσiso : IsIso σ.1)
    (hσ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t u.f),
      NeronModelInfra.schemeHomOverComp (u.L.mul t x y) σ =
        u.L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ))
    (hpol : ∀ s : ↥(Spec (CommRingCat.of S)), ∃ U : (Spec (CommRingCat.of S)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (u.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ.1).obj u.pol) ≅
        (Scheme.Modules.pullback (u.f ⁻¹ᵁ U).ι).obj u.pol)) :
    ∃ σ' : SchemeHomOver u'.f u'.f, IsIso σ'.1 ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t u'.f),
        NeronModelInfra.schemeHomOverComp (u'.L.mul t x y) σ' =
          u'.L.mul t (NeronModelInfra.schemeHomOverComp x σ') (NeronModelInfra.schemeHomOverComp y σ')) ∧
      (∀ s : ↥(Spec (CommRingCat.of S')), ∃ U : (Spec (CommRingCat.of S')).Opens, s ∈ U ∧
        Nonempty ((Scheme.Modules.pullback (u'.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ'.1).obj u'.pol) ≅
          (Scheme.Modules.pullback (u'.f ⁻¹ᵁ U).ι).obj u'.pol)) ∧
      σ'.1 ≫ gA = gA ≫ σ.1 := by sorry
