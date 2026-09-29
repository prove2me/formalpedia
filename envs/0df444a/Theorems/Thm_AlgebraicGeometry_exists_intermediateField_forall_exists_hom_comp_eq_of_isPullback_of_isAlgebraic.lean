-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_intermediateField_forall_exists_hom_comp_eq_of_isPullback_of_isAlgebraic
-- name    : AlgebraicGeometry.exists_intermediateField_forall_exists_hom_comp_eq_of_isPullback_of_isAlgebraic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/27eb723c-54a2-5b4d-994e-0810f9c227e5
-- title:
--   Spreading out a K-morphism of models to cofinal levels
-- statement:
--   Let $K/k$ be an algebraic extension of fields and let $L$ be an intermediate field of $K/k$ that is finite-dimensional over $k$. Let $X, Y, X_0, Y_0$ be schemes (in the zeroth universe) with structure morphisms $f_X : X \to \operatorname{Spec} K$, $f_Y : Y \to \operatorname{Spec} K$, $f_{X_0} : X_0 \to \operatorname{Spec} L$ and $f_{Y_0} : Y_0 \to \operatorname{Spec} L$, where the underlying space of $X_0$ is compact and quasi-separated and $f_{Y_0}$ is locally of finite type. Assume given $g_X : X \to X_0$ and $g_Y : Y \to Y_0$ making the squares formed with $f_X, f_{X_0}$, resp. $f_Y, f_{Y_0}$, and $\operatorname{Spec}$ of the inclusion $L \to K$ pullback squares, and a morphism $\varphi : X \to Y$ with $\varphi$ followed by $f_Y$ equal to $f_X$. Then there is an intermediate field $L_\varphi$ of $K/k$, finite-dimensional over $k$ and containing $L$, such that for every intermediate field $L'' \supseteq L_\varphi$, every ring homomorphism $j : L \to L''$ compatible with the inclusions of $L$ and $L''$ into $K$, and every pair of $L''$-schemes $f_{X_2} : X_2 \to \operatorname{Spec} L''$, $f_{Y_2} : Y_2 \to \operatorname{Spec} L''$ interpolating the given data — that is, morphisms $r_X : X \to X_2$, $q_X : X_2 \to X_0$ and $r_Y : Y \to Y_2$, $q_Y : Y_2 \to Y_0$ whose squares over $\operatorname{Spec}$ of $L'' \to K$ and of $j$ are pullback squares and which satisfy $q_X \circ r_X = g_X$ and $q_Y \circ r_Y = g_Y$ — there exists $\varphi_2 : X_2 \to Y_2$ with $\varphi_2$ followed by $f_{Y_2}$ equal to $f_{X_2}$ and $\varphi_2 \circ r_X = r_Y \circ \varphi$.
--
--   This is the spreading-out statement of EGA IV 8.8.2(i) for the filtered union $K = \bigcup L''$ of finite subextensions, phrased with models presented by arbitrary cartesian squares rather than by chosen pullback objects, and in a form valid simultaneously at every level and every refined model beyond one finite threshold, so that finitely many descended morphisms can be realised on a single common model. It is used in the construction of a relative group law on Jacobians of good reduction and in descending the action producing fake elliptic curves in the Čerednik–Drinfeld setting; the existence statement at one finite level is [`AlgebraicGeometry.exists_intermediateField_finiteDimensional_comp_pullback_map_eq_of_isAlgebraic`](thm.html#AlgebraicGeometry.exists_intermediateField_finiteDimensional_comp_pullback_map_eq_of_isAlgebraic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_intermediateField_forall_exists_hom_comp_eq_of_isPullback_of_isAlgebraic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_intermediateField_forall_exists_hom_comp_eq_of_isPullback_of_isAlgebraic
    (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (L : IntermediateField k K) [FiniteDimensional k ↥L]
    {X Y X₀ Y₀ : Scheme.{0}}
    (fX : X ⟶ Spec (CommRingCat.of K)) (fY : Y ⟶ Spec (CommRingCat.of K))
    (fX₀ : X₀ ⟶ Spec (CommRingCat.of ↥L)) (fY₀ : Y₀ ⟶ Spec (CommRingCat.of ↥L))
    [CompactSpace ↥X₀] [QuasiSeparatedSpace ↥X₀] [LocallyOfFiniteType fY₀]
    (gX : X ⟶ X₀) (hgX : IsPullback gX fX fX₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥L K))))
    (gY : Y ⟶ Y₀) (hgY : IsPullback gY fY fY₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥L K))))
    (φ : X ⟶ Y) (hφ : φ ≫ fY = fX) :
    ∃ (Lφ : IntermediateField k K) (_ : FiniteDimensional k ↥Lφ) (_ : L ≤ Lφ),
      ∀ (L'' : IntermediateField k K) (_ : Lφ ≤ L'')
        (j : ↥L →+* ↥L'') (_ : ∀ x : ↥L, ((j x : ↥L'') : K) = (x : K))
        (X₂ Y₂ : Scheme.{0}) (fX₂ : X₂ ⟶ Spec (CommRingCat.of ↥L'')) (fY₂ : Y₂ ⟶ Spec (CommRingCat.of ↥L''))
        (rX : X ⟶ X₂) (_ : IsPullback rX fX fX₂ (Spec.map (CommRingCat.ofHom (algebraMap ↥L'' K))))
        (qX : X₂ ⟶ X₀) (_ : IsPullback qX fX₂ fX₀ (Spec.map (CommRingCat.ofHom j))) (_ : rX ≫ qX = gX)
        (rY : Y ⟶ Y₂) (_ : IsPullback rY fY fY₂ (Spec.map (CommRingCat.ofHom (algebraMap ↥L'' K))))
        (qY : Y₂ ⟶ Y₀) (_ : IsPullback qY fY₂ fY₀ (Spec.map (CommRingCat.ofHom j))) (_ : rY ≫ qY = gY),
        ∃ φ₂ : X₂ ⟶ Y₂, φ₂ ≫ fY₂ = fX₂ ∧ rX ≫ φ₂ = φ ≫ rY := by sorry
