-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES
-- name    : AlgebraicGeometry.OModulePresheaf.eulerChar_eq_add_of_affSES
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/66c55966-4fbc-55ae-9654-a86646654e8c
-- title:
--   Additivity of the Čech Euler characteristic in short exact sequences
-- statement:
--   Let $k$ be a field, $V$ a scheme and $\pi : V \to \operatorname{Spec} k$ a separated morphism, and let $F_1, F_2, F_3$ be objects of `OModulePresheaf π`, that is, assignments of a $k$-module to each open $U \subseteq V$ carrying a compatible $\Gamma(V,U)$-module structure, together with $k$-linear restriction maps that are semilinear over the restriction of sections and satisfy the identities for the identity inclusion and for composites. Let $S$ be an `AffSES F₁ F₂ F₃`: morphisms $F_1 \to F_2$ and $F_2 \to F_3$ given by families of $k$-linear, $\Gamma(V,U)$-semilinear maps indexed by the affine opens $U$ of $V$ and commuting with restriction along inclusions of affine opens, such that on every affine open the first map is injective, the second surjective, and the range of the first equals the kernel of the second. Let $K$ be an ordered affine cover of $V$: a finite linearly ordered index type $\iota$ and affine opens $U_i$ with $\bigsqcup_i U_i = \top$. Assume for each $j$ that `F_j.CechFinite K` holds, i.e. $H^0$ and every $\ker d^{i+1}/\operatorname{im} d^i$ of the alternating Čech complex is a finite-dimensional $k$-vector space. Then the Euler characteristics, the alternating sums $\sum_{i<\#\iota}(-1)^i\dim_k$ of these cohomology spaces, satisfy $\chi(F_2) = \chi(F_1) + \chi(F_3)$.
--
--   This is the additivity of the Euler characteristic of alternating Čech cohomology along a short exact sequence that is exact on affine opens, the separatedness of $\pi$ guaranteeing affineness of the finite intersections of cover members. It is the basic bookkeeping device for the Euler-characteristic computations used further on, such as the comparison of $\chi$ of successive twists and tensor powers and the resulting degree bounds.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.eulerChar_eq_add_of_affSES
    {k : Type u} [Field k] {V : Scheme.{u}} {π : V ⟶ Spec (.of k)} [IsSeparated π]
    {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (K : V.OrderedAffineCover)
    (h₁ : F₁.CechFinite K) (h₂ : F₂.CechFinite K) (h₃ : F₃.CechFinite K) :
    F₂.eulerChar K = F₁.eulerChar K + F₃.eulerChar K := by sorry
