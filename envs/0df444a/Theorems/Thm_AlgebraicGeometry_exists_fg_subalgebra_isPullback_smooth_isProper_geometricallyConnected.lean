-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_smooth_isProper_geometricallyConnected
-- name    : AlgebraicGeometry.exists_fg_subalgebra_isPullback_smooth_isProper_geometricallyConnected
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/14d487d9-2f1b-5ca3-80f9-072a93cc8c68
-- title:
--   Descent of a smooth proper connected-fibred morphism to a finitely generated base
-- statement:
--   Let $S$ be a commutative ring and let $f : Z \to \operatorname{Spec} S$ be a morphism of schemes which is smooth (`Smooth f`) and proper (`IsProper f`), and assume that for every algebraically closed field $k$ (in the ambient universe) and every ring homomorphism $x : S \to k$ the underlying topological space of the fibre product $Z \times_{\operatorname{Spec} S} \operatorname{Spec} k$, formed along $\operatorname{Spec}$ of $x$, is a connected space (in particular nonempty). Then there exist a subalgebra $S_1 \subseteq S$ over $\mathbb{Z}$ which is finitely generated, a scheme $Z_1$, a morphism $f_1 : Z_1 \to \operatorname{Spec} S_1$ and a morphism $g_1 : Z \to Z_1$ such that the square formed by $g_1$, $f$, $f_1$ and $\operatorname{Spec}$ of the inclusion $S_1 \to S$ is commutative and cartesian, i.e. $g_1$ followed by $f_1$ equals $f$ followed by $\operatorname{Spec}(S_1 \to S)$ and $Z$ is the fibre product $Z_1 \times_{\operatorname{Spec} S_1} \operatorname{Spec} S$ via $g_1$ and $f$, and such that $f_1$ is smooth, proper, and satisfies the predicate `GeometricallyConnected`.
--
--   This is the spreading-out (approximation) step: a smooth proper morphism with connected geometric fibres over an arbitrary base descends, together with these three properties, to a finitely generated — hence noetherian and of finite type over $\mathbb{Z}$ — subalgebra of the base. It feeds [`AlgebraicGeometry.exists_fg_subalgebra_isPullback_smooth_isProper_of_isClosedImmersion_proj`](thm.html#AlgebraicGeometry.exists_fg_subalgebra_isPullback_smooth_isProper_of_isClosedImmersion_proj), where the projective embedding and the marked sections of a framed polarised abelian scheme are descended as well.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_smooth_isProper_geometricallyConnected.lean

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_fg_subalgebra_isPullback_smooth_isProper_geometricallyConnected
    {S : Type u} [CommRing S] {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of S))
    (hsm : Smooth f) (hpr : IsProper f)
    (hconn : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : S →+* k),
      ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x)))) :
    ∃ (S₁ : Subalgebra ℤ S) (_ : S₁.FG) (Z₁ : Scheme.{u}) (f₁ : Z₁ ⟶ Spec (CommRingCat.of ↥S₁)) (g₁ : Z ⟶ Z₁),
      IsPullback g₁ f f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥S₁ S))) ∧
      Smooth f₁ ∧ IsProper f₁ ∧ GeometricallyConnected f₁ := by sorry
