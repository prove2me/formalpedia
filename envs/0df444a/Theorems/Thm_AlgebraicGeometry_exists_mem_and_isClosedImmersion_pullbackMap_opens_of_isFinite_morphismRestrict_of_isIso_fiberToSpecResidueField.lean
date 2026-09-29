-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_mem_and_isClosedImmersion_pullbackMap_opens_of_isFinite_morphismRestrict_of_isIso_fiberToSpecResidueField
-- name    : AlgebraicGeometry.exists_mem_and_isClosedImmersion_pullbackMap_opens_of_isFinite_morphismRestrict_of_isIso_fiberToSpecResidueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/48786912-a23a-536d-99d4-86322ee064d1
-- title:
--   Closed immersion over a neighbourhood from fibrewise isomorphisms
-- statement:
--   Let $X$, $Y$, $Z$ be schemes, and let $p : Z \to Y$, $q : X \to Y$ and $h : Z \to X$ be morphisms with $h$ followed by $q$ equal to $p$, so that $h$ is a morphism over $Y$; both $p$ and $q$ are assumed proper, flat and locally of finite presentation. Let $y$ be a point of $Y$ and $V_0$ an open subscheme of $Y$ containing $y$. Assume that the restriction of $h$ over the open $q^{-1}(V_0)$ of $X$, namely $h \mid_{q^{-1}(V_0)} : h^{-1}(q^{-1}(V_0)) \to q^{-1}(V_0)$, is a finite morphism, and that for every point $x$ of $X$ with $q(x) = y$ the canonical morphism from the scheme-theoretic fibre of $h$ at $x$ to $\operatorname{Spec}\kappa(x)$ is an isomorphism. Then there is an open subscheme $V$ of $Y$ containing $y$ such that the morphism $Z \times_Y V \to X \times_Y V$ induced by $h$ and the identity of $V$ (via the open immersion $V \hookrightarrow Y$) is a closed immersion.
--
--   This is the local criterion that a morphism which is finite over a neighbourhood of $y$ and whose scheme-theoretic fibres over the points of $X$ above $y$ are single reduced points becomes a closed immersion after base change to a smaller neighbourhood of $y$ (EGA IV 18.12.6 in the proper flat setting). It feeds the companion statement [`AlgebraicGeometry.exists_mem_and_isClosedImmersion_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField`](thm.html#AlgebraicGeometry.exists_mem_and_isClosedImmersion_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField), where the fibrewise hypothesis is supplied in terms of residue-field base changes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_mem_and_isClosedImmersion_pullbackMap_opens_of_isFinite_morphismRestrict_of_isIso_fiberToSpecResidueField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_mem_and_isClosedImmersion_pullbackMap_opens_of_isFinite_morphismRestrict_of_isIso_fiberToSpecResidueField
    {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X) (w : h ≫ q = p)
    [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    [IsProper q] [Flat q] [LocallyOfFinitePresentation q]
    (y : Y) (V₀ : Y.Opens) (hy₀ : y ∈ V₀) (hfin : IsFinite (h ∣_ (q ⁻¹ᵁ V₀)))
    (hfib : ∀ x : X, q.base x = y → IsIso (h.fiberToSpecResidueField x)) :
    ∃ V : Y.Opens, y ∈ V ∧
      IsClosedImmersion (pullback.map p V.ι q V.ι h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])) := by sorry
