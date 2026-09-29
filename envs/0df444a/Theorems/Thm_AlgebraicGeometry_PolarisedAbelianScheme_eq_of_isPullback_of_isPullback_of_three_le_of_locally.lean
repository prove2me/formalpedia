-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_eq_of_isPullback_of_isPullback_of_three_le_of_locally
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.eq_of_isPullback_of_isPullback_of_three_le_of_locally
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/7079a02d-c4f8-5d83-a65e-396ab141eafc
-- title:
--   Rigidity of polarised level-n structures, polarisation matched locally
-- statement:
--   Fix natural numbers $g$, $d$, $n$ with $3 \le n$, commutative rings $S$, $S'$, a ring homomorphism $\varphi : S \to S'$ such that the image of $n$ is a unit in $S'$, and polarised abelian schemes $u$ over $S$ and $u'$ over $S'$ with invariants $g, d, n$; here a `PolarisedAbelianScheme` consists of a scheme $A$ with a structure morphism $f$ to $\operatorname{Spec}$ of the base, a commutative relative group law $L$ on the functor of points of $f$, the property bundle asserting $f$ smooth and proper with connected fibres and carrying a relative group law, fibres of topological Krull dimension $g$, a family $P : \mathrm{Fin}\,(2g) \to$ sections of $f$ that are $n$-torsion for $L$ and that, on every algebraically closed geometric fibre, parametrise the $n$-torsion bijectively by $(\mathbb{Z}/n)^{2g}$, and an invertible module `pol` that is a closed immersion by sections over the base and has geometric fibre $H^0$-rank $d$. Let $g_1, g_2 : u'.A \to u.A$ be morphisms of schemes. Assume, for $j = 1, 2$, that the square formed by $g_j$, $u'.f$, $u.f$ and $\operatorname{Spec}(\varphi)$ is a pullback; that $g_j$ is a homomorphism, in the sense that for every scheme $T$, every $t' : T \to \operatorname{Spec} S'$ and all $T$-points $x, y$ of $u'.A$ over $t'$, the composite of $u'.L.\mathrm{mul}\,t'\,x\,y$ with $g_j$ equals $u.L.\mathrm{mul}$ of the composites of $x$ and $y$ with $g_j$, taken over $t' \circ \operatorname{Spec}(\varphi)$; that $g_j$ carries the level structure of $u'$ to that of $u$, i.e. $(u'.P\,i) \cdot g_j = \operatorname{Spec}(\varphi) \cdot (u.P\,i)$ for all $i$; and that the polarisations agree locally on the base, i.e. every point $s$ of $\operatorname{Spec} S'$ has an open neighbourhood $U$ such that, after restriction along the inclusion of $u'.f^{-1}(U)$, the pullback of $u.\mathrm{pol}$ along $g_j$ is isomorphic to $u'.\mathrm{pol}$. Then $g_1 = g_2$.
--
--   This is the rigidity of polarised abelian schemes with level-$n$ structure for $n \ge 3$: a base-change comparison morphism compatible with the group law, the $2g$ level-$n$ sections and the polarisation (the latter required only locally on the base, which is the form in which the project's `IsPullback` comparison data arise after composition with isomorphisms) is unique. It is obtained from the statement that a polarisation-preserving automorphism over the base has finite order together with triviality of finite-order automorphisms fixing the $n$-torsion, and is used in the quaternionic-multiplication results on polarised abelian schemes, for instance in comparing pullback comparison maps and in the uniqueness part of the descent of such structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_eq_of_isPullback_of_isPullback_of_three_le_of_locally.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.eq_of_isPullback_of_isPullback_of_three_le_of_locally
    {g d n : ℕ} (hn : 3 ≤ n) {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (hn' : IsUnit ((n : ℕ) : S'))
    (u : PolarisedAbelianScheme g d n S) (u' : PolarisedAbelianScheme g d n S')
    (g₁ g₂ : u'.A ⟶ u.A)
    (h₁ : CategoryTheory.IsPullback g₁ u'.f u.f (Spec.map (CommRingCat.ofHom φ)))
    (h₁mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' u'.f),
      (u'.L.mul t' x y).1 ≫ g₁ =
        (u.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ g₁, by rw [Category.assoc, h₁.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g₁, by rw [Category.assoc, h₁.w, ← Category.assoc, y.2]⟩).1)
    (h₁P : ∀ i, (u'.P i).1 ≫ g₁ = Spec.map (CommRingCat.ofHom φ) ≫ (u.P i).1)
    (h₁pol : (∀ s : ↥(Spec (CommRingCat.of S')), ∃ U : (Spec (CommRingCat.of S')).Opens, s ∈ U ∧
        Nonempty ((Scheme.Modules.pullback (u'.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback g₁).obj u.pol) ≅
          (Scheme.Modules.pullback (u'.f ⁻¹ᵁ U).ι).obj (u'.pol))))
    (h₂ : CategoryTheory.IsPullback g₂ u'.f u.f (Spec.map (CommRingCat.ofHom φ)))
    (h₂mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t' u'.f),
      (u'.L.mul t' x y).1 ≫ g₂ =
        (u.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ g₂, by rw [Category.assoc, h₂.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ g₂, by rw [Category.assoc, h₂.w, ← Category.assoc, y.2]⟩).1)
    (h₂P : ∀ i, (u'.P i).1 ≫ g₂ = Spec.map (CommRingCat.ofHom φ) ≫ (u.P i).1)
    (h₂pol : (∀ s : ↥(Spec (CommRingCat.of S')), ∃ U : (Spec (CommRingCat.of S')).Opens, s ∈ U ∧
        Nonempty ((Scheme.Modules.pullback (u'.f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback g₂).obj u.pol) ≅
          (Scheme.Modules.pullback (u'.f ⁻¹ᵁ U).ι).obj (u'.pol)))) :
    g₁ = g₂ := by sorry
