-- Prove2me | Theorems.Thm_ConnesGreen_canonical_omitted_integral_rows_finite_packet_bound
-- name    : ConnesGreen.canonical_omitted_integral_rows_finite_packet_bound
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T20:11:18.820746+00:00
-- url     : https://prove2.me/theorems/01f1e88d-07c7-4e4e-a906-01c0cdbe6891
-- title:
--   At most the selected packet size of actual omitted rows determines the positive-error certificate kernel
-- statement:
--   For strictly positive original error $\delta$, ONE finite set $G$ of ACTUAL omitted zero indices outside the SAME original cutoff satisfies $$|G|\le |S|.$$ For EVERY original coefficient $c$ satisfying $K_\delta c=0$, vanishing of all ORIGINAL integral rows in $G$ is equivalent to vanishing of EVERY ORIGINAL omitted actual row. The same $G$ is chosen before $c$. The bound depends only on the ORIGINAL selected negative packet size, retaining original multiplicities, pair signs and carrier. No injectivity of the omitted row family or arithmetic lower bound is asserted.
-- source:
--   monocap-tech/weil, compiling source c3e7b782afd23ef5076a93915265a6584646b5e7, exact declaration ConnesGreen.canonical_omitted_integral_rows_finite_packet_bound

import Definitions.Def_ConnesGreen_integral_sampling_row
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

import Theorems.Thm_ConnesGreen_canonical_certificate_quotient_dimension_le_packet_card
import Theorems.Thm_ConnesGreen_canonical_omitted_integral_rows_finite_modulo_gram_kernel
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier Matrix
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
open ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability

theorem ConnesGreen.canonical_omitted_integral_rows_finite_packet_bound
    (t : ℝ) (ht : 0 < t) (S F : Finset CriticalZeros) (δ : ℝ) (hδ : 0 < δ) :
    ∃ G : Finset CriticalZeros, G.card ≤ S.card ∧
      (∀ ρ ∈ G, ρ ∉ F) ∧
      ∀ c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ,
        canonicalFiniteIntegralCertificate t S F δ *ᵥ c = 0 →
        ((∀ ρ ∈ G, canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0) ↔
        ∀ ρ : CriticalZeros, ρ ∉ F → canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0) := by sorry
