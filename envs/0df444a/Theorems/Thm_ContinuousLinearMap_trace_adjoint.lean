-- Prove2me | Theorems.Thm_ContinuousLinearMap_trace_adjoint
-- name    : ContinuousLinearMap.trace_adjoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:20:39.060478+00:00
-- url     : https://prove2.me/theorems/8a333e80-c62e-4d29-b085-7c26d43c2a81
-- title:
--   Continuous Linear Map: trace adjoint
-- statement:
--   The trace of the adjoint is the conjugate of the trace:
--   `tr G* = conj (tr G)`. (Compute both traces in an orthonormal basis.)
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/JohnIngredients.lean#L151-L159
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/JohnIngredients.lean#L151-L159

module
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.Normed.Module.Span
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Definitions.Def_BasicResults_JohnIngredients
set_option autoImplicit true
@[expose] public section
public section
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E] [CompleteSpace E]

theorem ContinuousLinearMap.trace_adjoint (G : E →L[𝕜] E) :
    LinearMap.trace 𝕜 E ((ContinuousLinearMap.adjoint G : E →L[𝕜] E) : E →ₗ[𝕜] E)
      = starRingEnd 𝕜 (LinearMap.trace 𝕜 E (G : E →ₗ[𝕜] E)) := by sorry
