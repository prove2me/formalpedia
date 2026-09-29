-- Prove2me | Theorems.Thm_AlgebraicGeometry_range_subset_iff_isIso_of_isPullback_of_forall_mem_iff_isIso_fibre
-- name    : AlgebraicGeometry.range_subset_iff_isIso_of_isPullback_of_forall_mem_iff_isIso_fibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/c1113204-8d41-56aa-a5ad-90e7b4b50931
-- title:
--   Universality of the fibrewise-isomorphism locus U
-- statement:
--   Let $p : \mathcal{Z} \to Y$, $q : \mathcal{X} \to Y$ be morphisms of schemes and let $h : \mathcal{Z} \to \mathcal{X}$ satisfy $q \circ h = p$, so $h$ is a morphism over $Y$. Let $U$ be an open subscheme of $Y$ such that: (i) for every point $y$ of $Y$, $y$ lies in $U$ if and only if the canonical morphism $\mathcal{Z} \times_Y \operatorname{Spec} \kappa(y) \to \mathcal{X} \times_Y \operatorname{Spec} \kappa(y)$ induced by $h$ and the identity of $\operatorname{Spec} \kappa(y)$, where $\operatorname{Spec} \kappa(y) \to Y$ is the canonical morphism from the residue field at $y$, is an isomorphism; and (ii) the canonical morphism $\mathcal{Z} \times_Y U \to \mathcal{X} \times_Y U$ induced by $h$ and the identity, along the open immersion $U \hookrightarrow Y$, is an isomorphism. Let now $t : T \to Y$ be arbitrary, and let $Z$, $X'$ be schemes fitting into cartesian squares: $e_Z : Z \to \mathcal{Z}$, $p_Z : Z \to T$ with the square $(e_Z, p_Z, p, t)$ a pullback, and $e_X : X' \to \mathcal{X}$, $q_X : X' \to T$ with $(e_X, q_X, q, t)$ a pullback. Let $\varphi : Z \to X'$ satisfy $q_X \circ \varphi = p_Z$ and $e_X \circ \varphi = h \circ e_Z$, i.e. $\varphi$ realises the base change of $h$ along $t$. Then the set-theoretic image of $t$ is contained in $U$ if and only if $\varphi$ is an isomorphism.
--
--   This is the universal property of the open locus over which a morphism of $Y$-schemes becomes an isomorphism: membership of the image of a test morphism $t$ in $U$ is equivalent to the base-changed morphism being an isomorphism, for any choice of cartesian models of the two base changes. It is used in the construction of the scheme representing the functor of morphisms over a base, where the representing object is cut out of a Hilbert scheme by such an open locus and the criterion identifies the points of that locus with graphs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_range_subset_iff_isIso_of_isPullback_of_forall_mem_iff_isIso_fibre.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.range_subset_iff_isIso_of_isPullback_of_forall_mem_iff_isIso_fibre
    {𝒳 Y 𝒵 : Scheme.{u}} (p : 𝒵 ⟶ Y) (q : 𝒳 ⟶ Y) (h : 𝒵 ⟶ 𝒳) (w : h ≫ q = p)
    (U : Y.Opens)
    (hU : ∀ y : Y, y ∈ (U : Set Y) ↔
      IsIso (pullback.map p (Y.fromSpecResidueField y) q (Y.fromSpecResidueField y) h (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])))
    (hUiso : IsIso (pullback.map p U.ι q U.ι h (𝟙 _) (𝟙 _) (by rw [Category.comp_id, w])
      (by rw [Category.comp_id, Category.id_comp])))
    {T Z X' : Scheme.{u}} (t : T ⟶ Y)
    (pZ : Z ⟶ T) (eZ : Z ⟶ 𝒵) (hZ : IsPullback eZ pZ p t)
    (qX : X' ⟶ T) (eX : X' ⟶ 𝒳) (hX : IsPullback eX qX q t)
    (φ : Z ⟶ X') (hφ₁ : φ ≫ qX = pZ) (hφ₂ : φ ≫ eX = eZ ≫ h) :
    Set.range t.base ⊆ (U : Set Y) ↔ IsIso φ := by sorry
