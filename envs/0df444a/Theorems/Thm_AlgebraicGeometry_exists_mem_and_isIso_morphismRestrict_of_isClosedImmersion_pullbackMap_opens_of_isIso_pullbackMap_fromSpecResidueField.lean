-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_mem_and_isIso_morphismRestrict_of_isClosedImmersion_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField
-- name    : AlgebraicGeometry.exists_mem_and_isIso_morphismRestrict_of_isClosedImmersion_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/f44833f8-0c99-5190-8235-ab2a442527af
-- title:
--   Flat closed immersion, isomorphic on one fibre, is locally an isomorphism
-- statement:
--   Let $X$, $Y$, $Z$ be schemes (in the bottom universe), and let $p : Z \to Y$, $q : X \to Y$ and $h : Z \to X$ be morphisms with $h$ followed by $q$ equal to $p$. Assume both $p$ and $q$ are proper, flat and locally of finite presentation. Let $y$ be a point of $Y$ and suppose that the induced morphism of fibres $Z \times_Y \operatorname{Spec}\kappa(y) \to X \times_Y \operatorname{Spec}\kappa(y)$ — the canonical map between the pullbacks of $p$ and of $q$ along $Y.\mathrm{fromSpecResidueField}\ y$ determined by $h$ and the identity of $\operatorname{Spec}\kappa(y)$ — is an isomorphism. Let $V_1 \subseteq Y$ be an open subscheme containing $y$ and assume that the base change $Z \times_Y V_1 \to X \times_Y V_1$ of $h$ induced in the same way along the open immersion $V_1 \hookrightarrow Y$ is a closed immersion. Then for every point $x$ of $X$ with $q(x) = y$ there is an open subscheme $D \subseteq X$ containing $x$ such that the restriction $h \mid_D : h^{-1}(D) \to D$ is an isomorphism.
--
--   This is the local form of the classical criterion (EGA III₁ 4.6.7) that a closed immersion between flat, proper, finitely presented $Y$-schemes which is an isomorphism on the fibre over $y$ is an isomorphism over a neighbourhood of $y$; the conclusion here is an open neighbourhood in $X$ of a prescribed point of the fibre. It is used to obtain the corresponding statement over an open neighbourhood of $y$ in the base, in [`AlgebraicGeometry.exists_mem_and_isIso_pullbackMap_opens_of_isClosedImmersion_pullbackMap_opens`](thm.html#AlgebraicGeometry.exists_mem_and_isIso_pullbackMap_opens_of_isClosedImmersion_pullbackMap_opens).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_mem_and_isIso_morphismRestrict_of_isClosedImmersion_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_mem_and_isIso_morphismRestrict_of_isClosedImmersion_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField
    {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X) (w : h ≫ q = p)
    [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    [IsProper q] [Flat q] [LocallyOfFinitePresentation q]
    (y : Y) (hy : IsIso (pullback.map p (Y.fromSpecResidueField y) q (Y.fromSpecResidueField y) h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])))
    (V₁ : Y.Opens) (hyV₁ : y ∈ V₁)
    (hci : IsClosedImmersion (pullback.map p V₁.ι q V₁.ι h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])))
    (x : X) (hx : q.base x = y) :
    ∃ D : X.Opens, x ∈ D ∧ IsIso (h ∣_ D) := by sorry
