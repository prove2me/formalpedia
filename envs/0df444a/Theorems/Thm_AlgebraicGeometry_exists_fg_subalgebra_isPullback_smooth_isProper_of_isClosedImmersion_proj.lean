-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_smooth_isProper_of_isClosedImmersion_proj
-- name    : AlgebraicGeometry.exists_fg_subalgebra_isPullback_smooth_isProper_of_isClosedImmersion_proj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/4be21393-66c7-55fa-9962-59b89a25df0b
-- title:
--   Noetherian descent of a smooth proper projective scheme with section
-- statement:
--   Let $S$ be a commutative ring, $Z$ a scheme and $f : Z \to \operatorname{Spec} S$ a morphism that is smooth (`Smooth f`) and proper (`IsProper f`). Assume further: (i) for some $N$ there is a morphism $\iota : Z \to \operatorname{Proj}$ of the graded ring of homogeneous polynomials in $N+1$ variables over $S$ (i.e. projective $N$-space over $S$) which is a closed immersion and satisfies $\iota$ followed by the structure morphism `ProjSpace.π S N` equals $f$; (ii) for every algebraically closed field $k$ and every ring homomorphism $x : S \to k$, the underlying space of the pullback of $f$ along $\operatorname{Spec}(x)$ is connected (in particular nonempty); and (iii) a section $\varepsilon$ of $f$, that is a morphism $\operatorname{Spec} S \to Z$ whose composite with $f$ is the identity. Then there exist a finitely generated $\mathbb{Z}$-subalgebra $S_0 \subseteq S$, a scheme $Z_0$, a morphism $f_0 : Z_0 \to \operatorname{Spec} S_0$ and a morphism $g : Z \to Z_0$ such that the square formed by $g$, $f$, $f_0$ and $\operatorname{Spec}$ of the inclusion $S_0 \to S$ is cartesian, $f_0$ is smooth and proper, $f_0$ admits, for some $N_0$, a closed immersion $\iota_0$ into projective $N_0$-space over $S_0$ with $\iota_0$ followed by `ProjSpace.π S₀ N₀` equal to $f_0$, every geometric fibre of $f_0$ (pullback along $\operatorname{Spec}$ of a homomorphism $S_0 \to k$ with $k$ algebraically closed) is connected, and there is a section $\varepsilon_0$ of $f_0$ with $\varepsilon$ followed by $g$ equal to $\operatorname{Spec}$ of the inclusion followed by $\varepsilon_0$.
--
--   This is the Noetherian approximation (limit) step: a smooth proper projectively embedded scheme with a section and connected geometric fibres over an arbitrary base ring descends, together with all of this structure, to a finitely generated $\mathbb{Z}$-subalgebra of the base. It is used in the construction of relative group laws on Jacobians with good reduction, namely in the proof that the locus where a geometric fibre carries a relative group law is open and in the existence of a commutative relative group law with identity section given that all geometric fibres are abelian varieties.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_smooth_isProper_of_isClosedImmersion_proj.lean

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_fg_subalgebra_isPullback_smooth_isProper_of_isClosedImmersion_proj
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S))
    (hsm : Smooth f) (hpr : IsProper f)
    (hproj : ∃ (N : ℕ) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)),
      IsClosedImmersion ι ∧ ι ≫ ProjSpace.π S N = f)
    (hconn : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
      ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f) :
    ∃ (S₀ : Subalgebra ℤ S) (_ : S₀.FG) (Z₀ : Scheme.{u}) (f₀ : Z₀ ⟶ Spec (CommRingCat.of ↥S₀)) (g : Z ⟶ Z₀),
      IsPullback g f f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥S₀ S))) ∧
      Smooth f₀ ∧ IsProper f₀ ∧
      (∃ (N₀ : ℕ) (ι₀ : Z₀ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N₀ + 1)) ↥S₀)),
        IsClosedImmersion ι₀ ∧ ι₀ ≫ ProjSpace.π ↥S₀ N₀ = f₀) ∧
      (∀ (k : Type u) [Field k] [IsAlgClosed k] (x₀ : ↥S₀ →+* k),
        ConnectedSpace ↥(pullback f₀ (Spec.map (CommRingCat.ofHom x₀)))) ∧
      ∃ ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥S₀))) f₀,
        ε.1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap ↥S₀ S)) ≫ ε₀.1 := by sorry
