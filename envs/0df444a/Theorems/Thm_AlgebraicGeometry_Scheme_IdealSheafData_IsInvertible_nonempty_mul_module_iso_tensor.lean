-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/9641cffc-c458-5aa6-8c3e-7680f0eece5c
-- title:
--   Invertible ideal sheaves: 𝒪(-Z₁-Z₂)≅𝒪(-Z₁)⊗𝒪(-Z₂)
-- statement:
--   Let $X$ be a scheme and let $I$, $J$ be quasi-coherent ideal sheaf data on $X$ (the data of an ideal of $\Gamma(X,U)$ for each affine open $U$, compatible with localisation). Assume each of $I$ and $J$ satisfies `IsInvertible`: for every point $x$ of $X$ there are an affine open $U$ and a section $f \in \Gamma(X,U)$ with $x$ in the basic open $X.\mathrm{basicOpen}\,f$, together with an element $g$ of $\Gamma(X, X.\mathrm{affineBasicOpen}\,f)$ that is a non-zero-divisor and generates the ideal attached to $X.\mathrm{affineBasicOpen}\,f$, so the ideal is locally free of rank one on a cofinal family of affine basic opens. For an ideal sheaf datum $K$, the sheaf of $\mathcal{O}_X$-modules $K.\mathrm{module}$ is the kernel of the canonical map from the unit sheaf of modules $\mathcal{O}_X$ to the pushforward along the closed immersion of the associated closed subscheme of the unit sheaf of modules of that subscheme. The conclusion is that the type of isomorphisms $(I \cdot J).\mathrm{module} \cong I.\mathrm{module} \otimes J.\mathrm{module}$ in the monoidal category of sheaves of $\mathcal{O}_X$-modules is nonempty; no particular isomorphism is specified.
--
--   This is the multiplicativity of the ideal-sheaf construction $Z \mapsto \mathcal{O}_X(-Z)$ for invertible ideals: the product ideal, which cuts out the sum of the two closed subschemes, corresponds to the tensor product of the two invertible modules. It is used in the treatment of relative effective Cartier divisors on curves, where it yields $\mathcal{O}(D+E) \cong \mathcal{O}(D) \otimes \mathcal{O}(E)$ and, through that, the additivity underlying the relative Picard functor and degree computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor.lean

import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicCurve_RelCartier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor
    {X : Scheme.{u}} {I J : X.IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    Nonempty ((I * J).module ≅ I.module ⊗ J.module) := by sorry
