-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_of_isProper_of_flat
-- name    : AlgebraicGeometry.exists_scheme_represents_schemeHomOver_of_isProper_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/022e4e8e-3a6d-5d7c-8a71-b5329e40a583
-- title:
--   Representability of the relative morphism scheme Mor_S(X,Y)
-- statement:
--   Let $S$ be a commutative ring and let $X$, $Y$ be schemes, with morphisms $f : X \to \operatorname{Spec} S$ assumed proper, flat and locally of finite presentation, and $g : Y \to \operatorname{Spec} S$ assumed separated, flat and locally of finite presentation. Assume given a sheaf of modules $\mathcal{L}_X$ on $X$ that is invertible, in the sense that every point of $X$ has an open neighbourhood $U$ on which the restriction of $\mathcal{L}_X$ is isomorphic to the unit module sheaf of $U$, and that satisfies `ClosedImmersionBySections` for $f$: for some $N$ there are $N+1$ global sections of $\mathcal{L}_X$ and a morphism to $\operatorname{Proj}$ of the graded ring of homogeneous polynomials in $N+1$ variables over $S$ which commutes with $f$ and the structural projection, which trivialises $\mathcal{L}_X$ by the chosen section on each basic open preimage and matches the ratios of coordinates with the ratios of the sections, and which is a closed immersion; assume the same data $\mathcal{L}_Y$, invertible and a closed immersion by sections, for $g$. Then there exist a scheme $H$, a morphism $\pi_H : H \to \operatorname{Spec} S$, and an assignment $\mathrm{pt}$ which, for every commutative ring $S'$, every $s : \operatorname{Spec} S' \to \operatorname{Spec} S$ and every $\varphi : X \times_{\operatorname{Spec} S} \operatorname{Spec} S' \to Y$ satisfying $g \circ \varphi = s \circ \mathrm{pr}_2$, produces an element of $\mathrm{SchemeHomOver}\ s\ \pi_H$, that is a morphism $\operatorname{Spec} S' \to H$ whose composite with $\pi_H$ is $s$, such that: (i) for every ring homomorphism $\psi : S' \to S''$ and every $s''$ with $\operatorname{Spec}\psi$ followed by $s$ equal to $s''$, the underlying morphism attached to the base change of $\varphi$ along $\operatorname{Spec}\psi$ equals $\operatorname{Spec}\psi$ followed by the underlying morphism attached to $\varphi$; (ii) every element of $\mathrm{SchemeHomOver}\ s\ \pi_H$ arises as some $\mathrm{pt}\ S'\ s\ \varphi$; (iii) $\varphi$ is determined by $\mathrm{pt}\ S'\ s\ \varphi$; and $\pi_H$ is separated and locally of finite presentation.
--
--   This is the representability of the relative morphism functor $S' \mapsto \mathrm{Mor}_{S}(X \times_S S', Y)$ by a separated, locally finitely presented $S$-scheme, in the projective setting provided by the two closed immersions by sections; the bijection is stated concretely as a naturality clause together with surjectivity and injectivity of the comparison map on affine test schemes. It is used in the Néron-model and good-reduction layer of the project, where it supplies the finitely generated ideal cutting out the locus on which a base-changed morphism factors as required.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_of_isProper_of_flat.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.exists_scheme_represents_schemeHomOver_of_isProper_of_flat
    (S : Type) [CommRing S] {X Y : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of S))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [IsSeparated g] [Flat g] [LocallyOfFinitePresentation g]
    (𝓛X : X.Modules) (hX₁ : Scheme.Modules.IsInvertible 𝓛X) (hX₂ : Scheme.Modules.ClosedImmersionBySections 𝓛X f)
    (𝓛Y : Y.Modules) (hY₁ : Scheme.Modules.IsInvertible 𝓛Y) (hY₂ : Scheme.Modules.ClosedImmersionBySections 𝓛Y g) :
    ∃ (H : Scheme.{0}) (πH : H ⟶ Spec (CommRingCat.of S))
      (pt : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (φ : pullback f s ⟶ Y), φ ≫ g = pullback.snd f s ≫ s → SchemeHomOver s πH),

      (∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
          (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
          (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
          (φ : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s),
        (pt S'' s''
            (pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ))
                (by rw [Category.assoc, hs]; exact pullback.condition) ≫ φ)
            (by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd, Category.assoc, hs])).1 =
          Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s φ hφ).1) ∧

      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver s πH),
        ∃ (φ : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s), pt S' s φ hφ = x) ∧

      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (φ φ' : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s) (hφ' : φ' ≫ g = pullback.snd f s ≫ s),
        pt S' s φ hφ = pt S' s φ' hφ' → φ = φ') ∧
      IsSeparated πH ∧ LocallyOfFinitePresentation πH := by sorry
