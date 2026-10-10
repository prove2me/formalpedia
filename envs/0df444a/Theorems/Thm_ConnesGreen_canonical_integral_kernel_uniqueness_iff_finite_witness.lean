-- Prove2me | Theorems.Thm_ConnesGreen_canonical_integral_kernel_uniqueness_iff_finite_witness
-- name    : ConnesGreen.canonical_integral_kernel_uniqueness_iff_finite_witness
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-09T17:11:14.040706+00:00
-- url     : https://prove2.me/theorems/804b4120-8e46-40b1-ab26-2c55d5ab3719
-- title:
--   Original integral sampling uniqueness exactly admits a bounded finite actual witness
-- statement:
--   For the existing ORIGINAL Gram matrix $H$, original integral certificate matrix $K_\delta$, and omitted actual integral rows, the condition $$K_\delta c=0\ \text{and}\ R_\rho c=0\ (\rho\notin F)\ \Longrightarrow\ Hc=0\quad\text{for every }c$$ is equivalent to existence of a finite ACTUAL sampling set $G$ outside the SAME $F$, with $|G|\le|F|+|S|$, for which $$K_\delta c=0\ \text{and}\ R_\rho c=0\ (\rho\in G)\ \Longrightarrow\ Hc=0\quad\text{for every }c.$$ The accuracy $\delta$ is any real number. This proves an exact reduction of uniqueness to a finite witness, not uniqueness itself. Nonzero coefficients in the original singular Gram kernel are allowed.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/FiniteSamplingWitness.lean, exact declaration ConnesGreen.canonical_integral_kernel_uniqueness_iff_finite_witness, compiling source a5af8470c9220c0783752dac5c5a25fc842dbe0d

import Definitions.Def_ConnesGreen_integral_sampling_row

import Theorems.Thm_ConnesGreen_canonical_omitted_integral_rows_finite
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open Complex ConnesRZ ConnesRZFrontier Matrix
open scoped BigOperators InnerProductSpace lp Classical ComplexOrder
noncomputable section
open ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability

theorem ConnesGreen.canonical_integral_kernel_uniqueness_iff_finite_witness
    (t : ℝ) (S F : Finset CriticalZeros) (δ : ℝ) :
    (∀ c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ,
      canonicalFiniteIntegralCertificate t S F δ *ᵥ c = 0 →
      (∀ ρ : CriticalZeros, ρ ∉ F → canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0) →
      canonicalFiniteColumnKernel t S F *ᵥ c = 0) ↔
    (∃ G : Finset CriticalZeros, G.card ≤ F.card + S.card ∧
      (∀ ρ ∈ G, ρ ∉ F) ∧
      ∀ c : ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → ℂ,
        canonicalFiniteIntegralCertificate t S F δ *ᵥ c = 0 →
        (∀ ρ ∈ G, canonicalIntegralSamplingRow t S F ρ ⬝ᵥ c = 0) →
        canonicalFiniteColumnKernel t S F *ᵥ c = 0) := by sorry
