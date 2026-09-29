-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_hom_eq_zero_of_pullback_map_eq_zero_of_isIntegral
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.hom_eq_zero_of_pullback_map_eq_zero_of_isIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/2ab7093d-2847-5f4c-8505-a35e3ab7b8eb
-- title:
--   Vanishing of a morphism of invertible modules detected on a non-empty open
-- statement:
--   Let $X$ be a scheme which is integral, and let $\mathcal L$ and $\mathcal M$ be objects of the category `X.Modules` of sheaves of modules over the structure sheaf of $X$. Assume both satisfy the predicate `Scheme.Modules.IsInvertible`, that is: for every point $x$ of $X$ there is an open $U \subseteq X$ with $x \in U$ such that the pullback of the module along the open immersion $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules on $U$ (the structure sheaf viewed as a module over itself). Let $\varphi : \mathcal L \to \mathcal M$ be a morphism of such modules, let $U$ be an open subscheme of $X$ whose underlying set is non-empty, and suppose that the image of $\varphi$ under the pullback functor `Scheme.Modules.pullback U.ι` along the canonical open immersion $\iota_U : U \to X$ is the zero morphism. The conclusion is that $\varphi = 0$.
--
--   This is the standard torsion-freeness statement for invertible (more generally, locally free) modules on an integral scheme: such a module has no sections supported on a proper closed subset, so a morphism out of it is determined by its restriction to any non-empty open. It is used in the study of line bundles in the Picard-functor material, for instance in [`AlgebraicGeometry.Polarisation.subsingleton_sections_of_inPicZero_of_not_iso_unit`](thm.html#AlgebraicGeometry.Polarisation.subsingleton_sections_of_inPicZero_of_not_iso_unit) and [`AlgebraicGeometry.Polarisation.not_forall_nonempty_pullback_translate_tensor_iso_of_kernelTrivial_of_geomFibreH0Finrank_pos`](thm.html#AlgebraicGeometry.Polarisation.not_forall_nonempty_pullback_translate_tensor_iso_of_kernelTrivial_of_geomFibreH0Finrank_pos).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_hom_eq_zero_of_pullback_map_eq_zero_of_isIntegral.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.hom_eq_zero_of_pullback_map_eq_zero_of_isIntegral
    {X : Scheme} [IsIntegral X] {𝓛 𝓜 : X.Modules} (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (φ : 𝓛 ⟶ 𝓜) (U : X.Opens) (hU : (U : Set X).Nonempty)
    (h : (Scheme.Modules.pullback U.ι).map φ = 0) : φ = 0 := by sorry
