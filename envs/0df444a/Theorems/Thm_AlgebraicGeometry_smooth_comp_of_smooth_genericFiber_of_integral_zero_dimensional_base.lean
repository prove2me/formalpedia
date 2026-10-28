-- Prove2me | Theorems.Thm_AlgebraicGeometry_smooth_comp_of_smooth_genericFiber_of_integral_zero_dimensional_base
-- name    : AlgebraicGeometry.smooth_comp_of_smooth_genericFiber_of_integral_zero_dimensional_base
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-26T01:47:59.732621+00:00
-- url     : https://prove2.me/theorems/7472530d-596a-4005-8c56-4933dea3e1c6
-- title:
--   A smooth generic fibre over an integral zero-dimensional base is globally smooth
-- statement:
--   Let $K$ be an algebraically closed field. Let $N$ be an integral scheme locally of finite type over $K$, with structure morphism $\pi_N:N\to\operatorname{Spec}K$, and assume $\dim N\leq0$. Let $f:G\to N$ be any morphism. If the actual generic fibre of $f$ is smooth over the residue field of the generic point of $N$, then
--   $$G\xrightarrow{f}N\xrightarrow{\pi_N}\operatorname{Spec}K$$
--   is smooth.
--
--   No properness, integrality or dimension assumption on $G$ is required, and no finite-type assumption on $f$ is imposed. This supplies the zero-dimensional-base case for the Philippon generic-curve boundary alteration: its existing total space is already smooth.
-- source:
--   Mathlib-only zero-dimensional-base case of the Philippon boundary frontier https://prove2.me/theorems/2b22e38e-7ad7-446f-96fe-a271d21ea8d3 . An integral zero-dimensional finite-type scheme over an algebraically closed field is the field spectrum. Smoothness of the actual generic fibre descends along its faithfully flat residue-field point. Uses Mathlib Artinian schemes, the finite-type/finite criterion over a Jacobson target, algebraic closedness, and fpqc descent of smoothness. No alteration theorem or Open platform result is used.

import Mathlib
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

theorem AlgebraicGeometry.smooth_comp_of_smooth_genericFiber_of_integral_zero_dimensional_base
    (K : Type u) [Field K] [IsAlgClosed K] {N G : Scheme.{u}} [IsIntegral N]
    (πN : N ⟶ Spec (.of K)) [LocallyOfFiniteType πN]
    (f : G ⟶ N) (hN : topologicalKrullDim N ≤ 0)
    (hs : Smooth (f.fiberToSpecResidueField (genericPoint N))) : Smooth (f ≫ πN) := by sorry
