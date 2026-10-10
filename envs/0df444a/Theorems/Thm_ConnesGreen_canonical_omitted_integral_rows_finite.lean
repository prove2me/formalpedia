-- Prove2me | Theorems.Thm_ConnesGreen_canonical_omitted_integral_rows_finite
-- name    : ConnesGreen.canonical_omitted_integral_rows_finite
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T17:08:00.74699+00:00
-- url     : https://prove2.me/theorems/0a1918bf-2a72-4728-b449-b901f4ce9dc3
-- title:
--   All omitted actual integral rows have one uniformly sufficient bounded finite sampling set
-- statement:
--   For the ORIGINAL selected packet $S$, ORIGINAL cutoff $F$ and support parameter $t$, there exists ONE finite set $G$ of ACTUAL zeta-zero indices, entirely outside $F$, with $$|G|\le |F|+|S|,$$ such that for EVERY coefficient vector in the unchanged tagged actor coefficient space, $$R_\rho c=0\ (\rho\in G)\iff R_\rho c=0\ (\rho\notin F).$$ Each $R_\rho$ is the exact existing original integral positive sampling row, including its actual-zero multiplicities and pair signs. The set $G$ is chosen before the coefficient vector. The original $S$ and $F$ remain fixed; $G$ is a sampling set, not a replacement certificate cutoff. No sampling uniqueness is assumed.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/FiniteSamplingWitness.lean, exact declaration ConnesGreen.canonical_omitted_integral_rows_finite, compiling source a5af8470c9220c0783752dac5c5a25fc842dbe0d

import Definitions.Def_ConnesGreen_integral_sampling_row

import Theorems.Thm_WeilDefect_MarkerStability_finite_sampling_rows_determine_all
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier Matrix
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
open ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability

theorem ConnesGreen.canonical_omitted_integral_rows_finite
    (t : ℝ) (S F : Finset CriticalZeros) :
    ∃ G : Finset CriticalZeros, G.card ≤ F.card + S.card ∧
      (∀ ρ ∈ G, ρ ∉ F) ∧
      ∀ c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ,
        (∀ ρ ∈ G, canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0) ↔
        ∀ ρ : CriticalZeros, ρ ∉ F → canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0 := by sorry
