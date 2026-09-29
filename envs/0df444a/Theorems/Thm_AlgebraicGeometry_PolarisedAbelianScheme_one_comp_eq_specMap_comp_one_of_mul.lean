-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_one_comp_eq_specMap_comp_one_of_mul
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.one_comp_eq_specMap_comp_one_of_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/d8e44808-8d4b-580b-8998-8f845583c820
-- title:
--   Multiplicative comparison maps preserve the zero section
-- statement:
--   Fix natural numbers $g, d, n$, commutative rings $S$ and $S'$ (in the base universe) and a ring homomorphism $\varphi : S \to S'$. Let $u$ be a polarised abelian scheme of invariants $(g,d,n)$ over $S$ and $u'$ one over $S'$; each such datum consists of a scheme $u.A$ with a structure morphism $u.f$ to $\operatorname{Spec} S$ (resp. $u'.f$ to $\operatorname{Spec} S'$), a relative group law `u.L` giving a functorial group structure on the sections $\{\psi : T \to u.A \mid \psi \circ u.f = t\}$ for each morphism $t : T \to \operatorname{Spec} S$, together with commutativity, the smooth/proper/connected-fibres bundle, fibres of Krull dimension $g$, a system of $2g$ $n$-torsion sections generating the geometric $n$-torsion freely, and an invertible polarisation module with $d$-dimensional geometric fibre sections. Let $gA : u'.A \to u.A$ be a morphism making the square with $u'.f$, $u.f$ and $\operatorname{Spec}(\varphi)$ cartesian, and assume $gA$ is multiplicative on points: for every scheme $T$, every $t' : T \to \operatorname{Spec} S'$ and all sections $x, y$ of $u'.f$ over $t'$, the morphism underlying $u'.L.\mathrm{mul}\,t'\,x\,y$ followed by $gA$ equals the morphism underlying the product, under `u.L` over $t'$ followed by $\operatorname{Spec}(\varphi)$, of $x$ followed by $gA$ and $y$ followed by $gA$. The conclusion is that the unit section of `u'.L` over the identity of $\operatorname{Spec} S'$, followed by $gA$, equals $\operatorname{Spec}(\varphi)$ followed by the unit section of `u.L` over the identity of $\operatorname{Spec} S$.
--
--   This is the standard fact that a morphism of group objects (here: a map cartesian over the base change and multiplicative on points) carries the zero section to the base change of the zero section. It is used in the comparison of polarised abelian schemes under base change, in particular by the results on pullbacks of the polarisation module and by the descent statements for polarised abelian schemes over faithfully flat, respectively localisation-away, base changes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_one_comp_eq_specMap_comp_one_of_mul.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.one_comp_eq_specMap_comp_one_of_mul
    {g d n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S')
    (gA : u'.A ⟶ u.A) (hg : CategoryTheory.IsPullback gA u'.f u.f (Spec.map (CommRingCat.ofHom φ)))
    (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' u'.f),
      (u'.L.mul t' x y).1 ≫ gA =
        (u.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1) :
    (u'.L.one (𝟙 _)).1 ≫ gA = Spec.map (CommRingCat.ofHom φ) ≫ (u.L.one (𝟙 _)).1 := by sorry
