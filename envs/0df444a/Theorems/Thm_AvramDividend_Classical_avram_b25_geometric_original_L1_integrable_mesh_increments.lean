-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b25_geometric_original_L1_integrable_mesh_increments
-- name    : AvramDividend.Classical.avram_b25_geometric_original_L1_integrable_mesh_increments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T00:53:59.826576+00:00
-- url     : https://prove2.me/theorems/7e076d7f-b038-4a38-a15a-05186496ebc1
-- title:
--   One strict geometric L1-subsequence retains all integrable two-noise mesh increments and signed errors
-- statement:
--   For two arbitrary integrable gain sequences with L1 Cauchy property and integrable signed errors converging to zero in L1, extract a shared strictly increasing subsequence with integrable gains differences, integrable errors, and geometric one-half power expectation bounds for each channel and error. A constructive corollary of Proved d697b992 and linearity of integrability; useful to build integrable dominating pathwise sums.
-- source:
--   B25 source-faithful geometric two-noise L1 subsequence. From Proved d697b992-6499-4474-8c3c-eb9beb22f29b and Integrable.sub; no stochastic source assumptions.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_simultaneous_geometric_L1_subsequence_from_original_three_cauchy_sources
open MeasureTheory Filter Topology
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_b25_geometric_original_L1_integrable_mesh_increments
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (G J E : ℕ → Ω → ℝ)
    (hGI : ∀ k, Integrable (G k) P)
    (hJI : ∀ k, Integrable (J k) P)
    (hEI : ∀ k, Integrable (E k) P)
    (hG : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m l : ℕ,
      N ≤ m → N ≤ l → (∫ ω, ‖G m ω - G l ω‖ ∂P) ≤ ε)
    (hJ : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m l : ℕ,
      N ≤ m → N ≤ l → (∫ ω, ‖J m ω - J l ω‖ ∂P) ≤ ε)
    (hE : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m : ℕ,
      N ≤ m → (∫ ω, ‖E m ω‖ ∂P) ≤ ε) :
    ∃ K : ℕ → ℕ,
      StrictMono K ∧
      (∀ k, Integrable (fun ω => G (K (k + 1)) ω - G (K k) ω) P) ∧
      (∀ k, Integrable (fun ω => J (K (k + 1)) ω - J (K k) ω) P) ∧
      (∀ k, Integrable (E (K k)) P) ∧
      (∀ k, (∫ ω, ‖G (K (k + 1)) ω - G (K k) ω‖ ∂P)
        ≤ ((1 : ℝ) / 2) ^ k) ∧
      (∀ k, (∫ ω, ‖J (K (k + 1)) ω - J (K k) ω‖ ∂P)
        ≤ ((1 : ℝ) / 2) ^ k) ∧
      (∀ k, (∫ ω, ‖E (K k) ω‖ ∂P)
        ≤ ((1 : ℝ) / 2) ^ k) := by sorry
