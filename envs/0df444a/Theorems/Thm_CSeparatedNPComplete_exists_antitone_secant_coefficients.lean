-- Prove2me | Theorems.Thm_CSeparatedNPComplete_exists_antitone_secant_coefficients
-- name    : CSeparatedNPComplete.exists_antitone_secant_coefficients
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:45:55.710233+00:00
-- url     : https://prove2.me/theorems/f6fb2520-d5d7-5111-b31a-bc3144229a2e
-- title:
--   CSeparated NPComplete: exists antitone secant coefficients
-- statement:
--   Secant slopes along two decreasing finite sequences admit a decreasing extension
--   across indices where the two entries coincide. These coefficients give an exact
--   factorization of the corresponding differences of convex function values.
--
--   Source: https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/ConvexSlopes.lean#L39-L57
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete/ConvexSlopes.lean#L39-L57

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

theorem CSeparatedNPComplete.exists_antitone_secant_coefficients {n : ℕ} {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ConvexOn ℝ s f) (u v : Fin n → ℝ)
    (hu : Antitone u) (hv : Antitone v)
    (hu_mem : ∀ i, u i ∈ s) (hv_mem : ∀ i, v i ∈ s) :
    ∃ c : Fin n → ℝ, Antitone c ∧
      ∀ i, f (u i) - f (v i) = c i * (u i - v i) := by sorry
