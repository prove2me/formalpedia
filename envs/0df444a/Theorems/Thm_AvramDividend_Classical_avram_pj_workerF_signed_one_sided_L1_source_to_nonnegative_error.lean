-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerF_signed_one_sided_L1_source_to_nonnegative_error
-- name    : AvramDividend.Classical.avram_pj_workerF_signed_one_sided_L1_source_to_nonnegative_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T22:34:35.294025+00:00
-- url     : https://prove2.me/theorems/d4d7086c-0624-4d4d-a4d0-80179354a790
-- title:
--   Signed one-sided physical-grid L1 source yields nonnegative cutoff and vanishing-error certificate
-- statement:
--   Given any actual stopped Ito source furnishing a signed pointwise upper error K+E_k on the original event, an integrable spatial K with arbitrarily small L1 cost and integrable E_k whose L1 cost tends to zero, the absolute values |K| and |E_k| provide a nonnegative cutoff/error pair satisfying the original one-sided stopped upper estimate with unchanged smallness and L1 vanishing. No dividend or jump term is suppressed; the source itself must be proved separately.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerF_signed_one_sided_L1_source_to_nonnegative_error
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (V U K : Ω → ℝ) (E : ℕ → Ω → ℝ)
    (S : Set Ω) (ε : ℝ)
    (hKI : Integrable K P)
    (hKsmall : (∫ ω, |K ω| ∂P) ≤ ε / 4)
    (hEI : ∀ k, Integrable (E k) P)
    (hUpper : ∀ k, ∀ᵐ ω ∂P,
      ω ∈ S → V ω - U ω ≤ K ω + E k ω)
    (hVan : Tendsto (fun k => ∫ ω, |E k ω| ∂P)
      Filter.atTop (nhds (0 : ℝ))) :
    ∃ K' : Ω → ℝ, ∃ E' : ℕ → Ω → ℝ,
      Integrable K' P ∧
      (∫ ω, |K' ω| ∂P) ≤ ε / 4 ∧
      (∀ k, Integrable (E' k) P) ∧
      (∀ᵐ ω ∂P, 0 ≤ K' ω) ∧
      (∀ k, ∀ᵐ ω ∂P, 0 ≤ E' k ω) ∧
      (∀ k, ∀ᵐ ω ∂P, ω ∈ S →
        V ω - U ω ≤ K' ω + E' k ω) ∧
      Tendsto (fun k => ∫ ω, |E' k ω| ∂P)
        Filter.atTop (nhds (0 : ℝ)) := by sorry
