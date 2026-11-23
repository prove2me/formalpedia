-- Prove2me | Theorems.Thm_DedekindZeta_summable_of_bounded_fiber
-- name    : DedekindZeta.summable_of_bounded_fiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:45:35.653808+00:00
-- url     : https://prove2.me/theorems/d39aa904-8048-4180-9545-6fcbecc9ace9
-- title:
--   Dedekind Zeta: summable of bounded fiber
-- statement:
--   **Abstract bounded-fiber summability comparison.** If a real family `f` over
--   `ι` factors through a map `ψ : ι → κ` as `f i = c · h (ψ i)` with `c ≥ 0`, `h`
--   summable and nonnegative, and every fibre `ψ⁻¹ {k}` is finite with cardinality
--   bounded by a fixed `N`, then `f` is summable. (Each fibre contributes
--   `≤ N · c · h k`, and `∑ₖ h k < ∞`.)
--
--   Source: https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L2099-L2153
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean#L2099-L2153

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
set_option autoImplicit true
open NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open Filter Finset Asymptotics Topology
open scoped Real nonZeroDivisors
open DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped NNReal ENNReal

theorem DedekindZeta.summable_of_bounded_fiber {ι : Type*} {κ : Type*}
    {f : ι → ℝ} {h : κ → ℝ} {ψ : ι → κ} {c : ℝ} {N : ℕ}
    (hf : ∀ i, f i = c * h (ψ i)) (hc : 0 ≤ c) (hh : Summable h)
    (hhnn : ∀ k, 0 ≤ h k) (hfin : ∀ k, Finite {i // ψ i = k})
    (hcard : ∀ k, Nat.card {i // ψ i = k} ≤ N) :
    Summable f := by sorry
