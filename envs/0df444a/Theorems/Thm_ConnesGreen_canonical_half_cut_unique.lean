-- Prove2me | Theorems.Thm_ConnesGreen_canonical_half_cut_unique
-- name    : ConnesGreen.canonical_half_cut_unique
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T05:52:13.889386+00:00
-- url     : https://prove2.me/theorems/bf541fe3-245b-4b37-9daf-df55c7bb2ec4
-- title:
--   The original finite-packet inner half-bound cutoff is unique
-- statement:
--   For the same unchanged finite actual-zero packet $S$, if $c,d\ge R$ both characterize the successful original half-bound windows by
--   $$\tfrac12 I\le G_S(T)\ \Longleftrightarrow\ T\le c,\qquad
--   \tfrac12 I\le G_S(T)\ \Longleftrightarrow\ T\le d\quad(T>0),$$
--   then $c=d$. Positivity of the original $R$ makes both endpoints positive. The first characterization gives success at $c$ and the second therefore gives $c\le d$. Reversing their roles gives $d\le c$. Antisymmetry proves uniqueness. This is uniqueness of the inner half-bound cutoff; it does not identify that cutoff with a separately prescribed critical endpoint.
-- source:
--   monocap-tech/weil at e6d17e3f8533cdffc6af82283874365e7d869f8e; WeilDefect/Connes/HalfWindowClassification.lean (new additive module), using unchanged original CriticalWindowBoundary and actor definitions.

import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

theorem ConnesGreen.canonical_half_cut_unique (S : Finset CriticalZeros)
    (c d : ℝ) (hc : positiveSupportRadius ≤ c) (hd : positiveSupportRadius ≤ d)
    (hcutc : (∀ T : ℝ, ∀ hT : 0 < T, ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S) ↔ T ≤ c))
    (hcutd : (∀ T : ℝ, ∀ hT : 0 < T, ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S) ↔ T ≤ d)) : c = d := by sorry
