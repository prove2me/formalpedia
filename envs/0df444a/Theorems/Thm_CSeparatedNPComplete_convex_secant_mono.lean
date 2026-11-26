-- Prove2me | Theorems.Thm_CSeparatedNPComplete_convex_secant_mono
-- name    : CSeparatedNPComplete.convex_secant_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:45:56.106841+00:00
-- url     : https://prove2.me/theorems/e2d64350-1bae-4426-a363-04ed381c4820
-- title:
--   CSeparated NPComplete: convex secant mono
-- statement:
--   Moving both endpoints of a nondegenerate secant to the right increases its slope.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/ConvexSlopes.lean#L19-L34
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/ConvexSlopes.lean#L19-L34

module
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Order.Monotone.Extension
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Definitions.Def_CSeparatedNPComplete_ConvexSlopes
set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete

theorem CSeparatedNPComplete.convex_secant_mono {s : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ s f)
    {x₁ x₂ y₁ y₂ : ℝ} (hx₁ : x₁ ∈ s) (hx₂ : x₂ ∈ s)
    (hy₁ : y₁ ∈ s) (hy₂ : y₂ ∈ s)
    (h₁ : x₁ ≠ y₁) (h₂ : x₂ ≠ y₂) (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) :
    (f y₁ - f x₁) / (y₁ - x₁) ≤ (f y₂ - f x₂) / (y₂ - x₂) := by sorry
