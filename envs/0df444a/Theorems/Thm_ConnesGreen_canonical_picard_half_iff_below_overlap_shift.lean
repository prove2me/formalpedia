-- Prove2me | Theorems.Thm_ConnesGreen_canonical_picard_half_iff_below_overlap_shift
-- name    : ConnesGreen.canonical_picard_half_iff_below_overlap_shift
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T03:48:23.269388+00:00
-- url     : https://prove2.me/theorems/beef55f9-dc3f-4cf9-98e5-5bf0e80c19ae
-- title:
--   Original Picard half-bound reduces exactly to accuracies below the arithmetic shift
-- statement:
--   Fix $0<T\le R$ and an unchanged finite packet $S$ of ACTUAL zeta-zero indices. The ORIGINAL Picard marker satisfies $$\tfrac12 I\le M_{T,S}\quad\Longleftrightarrow\quad\forall\delta\in(0,K_R],\ \exists F\text{ finite}:\ 0\le D_{T,S,F}(\delta).$$ The explicit nonnegative overlap shift $K_R$ is fixed BEFORE accuracy. The accepted above-shift construction supplies every $\delta>K_R$ with packet containment, reflection closure and COMPLETE tail payment. The preceding accepted cutoff completion restores those requirements for any finite nonnegative correction at smaller accuracies. This is an exact reduction of the unchanged original all-accuracy theorem, not its proof or an RH assertion.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/OverlapShiftCertificates.lean, exact declaration ConnesGreen.canonical_picard_half_iff_below_overlap_shift, compiling local source d80c1a8e4c7f0442e092ecaaf726d7aa26822229. Original arithmetic definitions, physical energy, actual prime powers and admissible test class retained.

import Definitions.Def_ConnesGreen_arithmetic_overlap_shift
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ContinuousLinearMap Set Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative ConnesGreen WeilDefect.MarkerStability

theorem ConnesGreen.canonical_picard_half_iff_below_overlap_shift
    (R T : ℝ) (hT : 0 < T) (hTR : T ≤ R) (S : Finset CriticalZeros) :
    ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S) ↔
    ∀ δ : ℝ, 0 < δ → δ ≤ arithmeticOverlapShift R →
      ∃ F : Finset CriticalZeros, 0 ≤ canonicalFiniteSelectedCorrection T hT S F δ := by sorry
