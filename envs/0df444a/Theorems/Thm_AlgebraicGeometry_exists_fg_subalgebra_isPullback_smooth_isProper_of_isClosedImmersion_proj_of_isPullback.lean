-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_smooth_isProper_of_isClosedImmersion_proj_of_isPullback
-- name    : AlgebraicGeometry.exists_fg_subalgebra_isPullback_smooth_isProper_of_isClosedImmersion_proj_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/20a8aae9-611b-5ef9-883d-7f04116a35ac
-- title:
--   Spreading out a smooth proper projective scheme with section
-- statement:
--   Let $S$ be a commutative ring and let $f : Z \to \operatorname{Spec} S$ be a morphism of schemes that is smooth and proper, such that for some $N$ there is a closed immersion $\iota : Z \to \mathbf{P}^N_S = \operatorname{Proj}$ of the graded ring of homogeneous polynomials in $N+1$ variables over $S$ with $\iota$ followed by the structure morphism `ProjSpace.π` equal to $f$, and such that for every algebraically closed field $k$ and every ring homomorphism $x : S \to k$ the underlying space of the fibre product of $f$ along $\operatorname{Spec} x$ is connected. Let $\varepsilon$ be a section of $f$, that is, a morphism $\operatorname{Spec} S \to Z$ composing with $f$ to the identity. Assume in addition given a finitely generated $\mathbb{Z}$-subalgebra $S_1 \subseteq S$, a scheme $Z_1$, a morphism $f_1 : Z_1 \to \operatorname{Spec} S_1$ and $g_1 : Z \to Z_1$ making the square formed by $g_1$, $f$, $f_1$ and $\operatorname{Spec}$ of $S_1 \to S$ cartesian, with $f_1$ smooth, proper and satisfying the predicate `GeometricallyConnected`. The conclusion asserts the existence of a finitely generated $\mathbb{Z}$-subalgebra $S_0 \subseteq S$, a scheme $Z_0$, a morphism $f_0 : Z_0 \to \operatorname{Spec} S_0$ and $g : Z \to Z_0$ such that the square formed by $g$, $f$, $f_0$ and $\operatorname{Spec}$ of $S_0 \to S$ is cartesian, $f_0$ is smooth and proper, $Z_0$ admits a closed immersion into $\mathbf{P}^{N_0}_{S_0}$ over $\operatorname{Spec} S_0$ for some $N_0$ (not necessarily the given $N$), every geometric fibre of $f_0$ over an algebraically closed field has connected underlying space, and there is a section $\varepsilon_0$ of $f_0$ with $\varepsilon$ followed by $g$ equal to $\operatorname{Spec}$ of $S_0 \to S$ followed by $\varepsilon_0$.
--
--   This is a spreading-out (approximation) statement in the style of EGA IV §8: a smooth proper projectively embedded $S$-scheme with a section and connected geometric fibres descends, together with its embedding, its section and the connectedness of its geometric fibres, to a finitely generated $\mathbb{Z}$-subalgebra of $S$. It is the step of the construction that upgrades an already-found finitely generated model $f_1$ to one carrying all the extra structure, and is used by [`AlgebraicGeometry.exists_fg_subalgebra_isPullback_smooth_isProper_of_isClosedImmersion_proj`](thm.html#AlgebraicGeometry.exists_fg_subalgebra_isPullback_smooth_isProper_of_isClosedImmersion_proj); the projective base-change input is [`AlgebraicGeometry.ProjSpace.isPullback_map`](thm.html#AlgebraicGeometry.ProjSpace.isPullback_map).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_smooth_isProper_of_isClosedImmersion_proj_of_isPullback.lean

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_fg_subalgebra_isPullback_smooth_isProper_of_isClosedImmersion_proj_of_isPullback
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S))
    (hsm : Smooth f) (hpr : IsProper f)
    (hproj : ∃ (N : ℕ) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)),
      IsClosedImmersion ι ∧ ι ≫ ProjSpace.π S N = f)
    (hconn : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
      ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    (S₁ : Subalgebra ℤ S) (hS₁ : S₁.FG) (Z₁ : Scheme.{u}) (f₁ : Z₁ ⟶ Spec (CommRingCat.of ↥S₁)) (g₁ : Z ⟶ Z₁)
    (hg₁ : IsPullback g₁ f f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥S₁ S))))
    (hsm₁ : Smooth f₁) (hpr₁ : IsProper f₁) (hgc₁ : GeometricallyConnected f₁) :
    ∃ (S₀ : Subalgebra ℤ S) (_ : S₀.FG) (Z₀ : Scheme.{u}) (f₀ : Z₀ ⟶ Spec (CommRingCat.of ↥S₀)) (g : Z ⟶ Z₀),
      IsPullback g f f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥S₀ S))) ∧
      Smooth f₀ ∧ IsProper f₀ ∧
      (∃ (N₀ : ℕ) (ι₀ : Z₀ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N₀ + 1)) ↥S₀)),
        IsClosedImmersion ι₀ ∧ ι₀ ≫ ProjSpace.π ↥S₀ N₀ = f₀) ∧
      (∀ (k : Type u) [Field k] [IsAlgClosed k] (x₀ : ↥S₀ →+* k),
        ConnectedSpace ↥(pullback f₀ (Spec.map (CommRingCat.ofHom x₀)))) ∧
      ∃ ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥S₀))) f₀,
        ε.1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap ↥S₀ S)) ≫ ε₀.1 := by sorry
