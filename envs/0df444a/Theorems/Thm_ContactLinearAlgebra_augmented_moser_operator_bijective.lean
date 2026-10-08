-- Prove2me | Theorems.Thm_ContactLinearAlgebra_augmented_moser_operator_bijective
-- name    : ContactLinearAlgebra.augmented_moser_operator_bijective
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T19:06:14.26035+00:00
-- url     : https://prove2.me/theorems/8dc9f885-808a-4140-a397-1c5f3a82e37d
-- title:
--   Augmented Moser operator is invertible
-- statement:
--   Let V and W be finite-dimensional real vector spaces, D:V→W a surjective linear map, a a covector on V nonzero on ker D, and b a bilinear form whose restriction to ker D ∩ ker a is left nondegenerate. Write V* and W* for the algebraic duals. The linear operator from V × ℝ × W* to V* × ℝ × W given by
--
--   $$ (u,\mu,\nu) \longmapsto \bigl(b(u,\cdot)-\mu a-\nu\circ D,\ a(u),\ D(u)\bigr) $$
--
--   is bijective. This fixed-space operator packages the constrained Moser equation and its normal multipliers, providing an invertible linear system suitable for smooth parameter dependence. Alternation of b is not required.
-- source:
--   Geiges, Contact geometry, https://arxiv.org/abs/math/0307242, proof of Theorem 2.20, printed p. 15, equations (2.1)-(2.2). Independent auxiliary formulation for smooth Moser selection; the linear-algebra and cutoff arguments are supplied in the accompanying proof. Smooth operator inversion and cutoff foundations use Mathlib ContDiff.Operations and BumpFunction.FiniteDimension at commit 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

set_option autoImplicit false

theorem ContactLinearAlgebra.augmented_moser_operator_bijective
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (D : V →ₗ[ℝ] W) (a : V →ₗ[ℝ] ℝ) (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hD : Function.Surjective D) (ha : ∃ v, D v = 0 ∧ a v ≠ 0)
    (hn : ∀ u, D u = 0 → a u = 0 →
      (∀ v, D v = 0 → a v = 0 → b u v = 0) → u = 0) :
    Function.Bijective (fun p : V × (ℝ × Module.Dual ℝ W) =>
      (b p.1 - p.2.1 • a - p.2.2.comp D, (a p.1, D p.1))) := by sorry
