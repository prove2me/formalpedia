-- Prove2me | Theorems.Thm_AlgebraicGeometry_eq_of_pullback_map_eq_pullback_map_of_isSeparated
-- name    : AlgebraicGeometry.eq_of_pullback_map_eq_pullback_map_of_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/71f61bae-2b5a-5403-ac06-baa6504ab2c5
-- title:
--   Base change along a field extension is faithful into separated targets
-- statement:
--   Let $k$ and $K$ be fields with $K$ a $k$-algebra, and let $\operatorname{Spec} K \to \operatorname{Spec} k$ denote the morphism of schemes induced by the structure map $k \to K$. Let $X$ and $Y$ be schemes equipped with morphisms $f_X : X \to \operatorname{Spec} k$ and $f_Y : Y \to \operatorname{Spec} k$, and assume $f_Y$ is separated (`IsSeparated fY`). Let $g_1, g_2 : X \to Y$ be two morphisms over $k$, that is, $g_1$ followed by $f_Y$ and $g_2$ followed by $f_Y$ both equal $f_X$. Assume finally that the two morphisms of fibre products
--   $$X \times_{\operatorname{Spec} k} \operatorname{Spec} K \longrightarrow Y \times_{\operatorname{Spec} k} \operatorname{Spec} K$$
--   obtained from $(g_1, \mathrm{id}_{\operatorname{Spec} K})$ and from $(g_2, \mathrm{id}_{\operatorname{Spec} K})$ over $\mathrm{id}_{\operatorname{Spec} k}$ (the canonical `pullback.map` morphisms for the stated commutativities) coincide. Then $g_1 = g_2$. No hypothesis is imposed on $X$, on the degree or algebraicity of $K/k$, or on $f_Y$ beyond separatedness.
--
--   This is the faithfulness, or uniqueness, half of descent of morphisms along a field extension: base change $- \times_k K$ is injective on $k$-morphisms into a scheme separated over $k$. It is used as the uniqueness clause in the Galois descent statements [`AlgebraicGeometry.exists_intermediateField_isGalois_galois_twist_comp_pullback_map_eq`](thm.html#AlgebraicGeometry.exists_intermediateField_isGalois_galois_twist_comp_pullback_map_eq) and [`AlgebraicGeometry.exists_unique_eq_pullback_map_of_forall_galois_twist_comp_eq`](thm.html#AlgebraicGeometry.exists_unique_eq_pullback_map_of_forall_galois_twist_comp_eq), and is isolated here because it requires none of their Galois or finiteness hypotheses.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_eq_of_pullback_map_eq_pullback_map_of_isSeparated.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.eq_of_pullback_map_eq_pullback_map_of_isSeparated
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X Y : Scheme.{u}) (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated fY]
    (g₁ g₂ : X ⟶ Y) (h₁ : g₁ ≫ fY = fX) (h₂ : g₂ ≫ fY = fX)
    (H : pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k K)))
            g₁ (𝟙 _) (𝟙 _) (by rw [Category.comp_id, h₁]) (by rw [Category.comp_id, Category.id_comp]) =
         pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY (Spec.map (CommRingCat.ofHom (algebraMap k K)))
            g₂ (𝟙 _) (𝟙 _) (by rw [Category.comp_id, h₂]) (by rw [Category.comp_id, Category.id_comp])) :
    g₁ = g₂ := by sorry
