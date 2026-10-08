-- Prove2me | Theorems.Thm_ConnesGreen_canonical_half_window_dichotomy
-- name    : ConnesGreen.canonical_half_window_dichotomy
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T05:52:19.039824+00:00
-- url     : https://prove2.me/theorems/e34d5210-9a2b-419b-a79b-ae005670d4ba
-- title:
--   Original finite packets have either all positive half-bound windows or a finite closed cutoff
-- statement:
--   For every unchanged finite packet $S$ of actual zeta zeros, write $G_S(T)$ for the original Picard marker and $R$ for positiveSupportRadius. We prove the exact alternative
--   $$\bigl(\forall T>0,\ \tfrac12 I\le G_S(T)\bigr)\quad\lor\quad\bigl(\exists c\ge R,\ \forall T>0,\ \tfrac12 I\le G_S(T)\ \Longleftrightarrow\ T\le c\bigr).$$
--   If not every positive window has the half-bound, choose a failed positive window $b$. Antitonicity of the original marker bounds the set of successful positive windows above by $b$. Its membership at $R>0$ makes this set nonempty. Its real supremum $c$ therefore satisfies $R\le c$. For every positive $T<c$, the supremum property provides a successful larger window; antitonicity transfers its half-bound to $T$. The accepted original all-smaller-windows closure theorem then supplies the half-bound at $c$ itself. Thus successful windows are exactly those at most $c$. Lean uses real conditional completeness, the original positive-window marker identity, accepted original antitonicity and boundary closure. No prescribed critical-endpoint identification, right-limit continuity or off-line separation hypothesis is added.
-- source:
--   monocap-tech/weil at e6d17e3f8533cdffc6af82283874365e7d869f8e; WeilDefect/Connes/HalfWindowClassification.lean (new additive module), using unchanged original CriticalWindowBoundary and actor definitions.

import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

theorem ConnesGreen.canonical_half_window_dichotomy (S : Finset CriticalZeros) :
    (∀ T : ℝ, ∀ hT : 0 < T, (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S) ∨
    ∃ c : ℝ, positiveSupportRadius ≤ c ∧ (∀ T : ℝ, ∀ hT : 0 < T, ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S) ↔ T ≤ c) := by sorry
