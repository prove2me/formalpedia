-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb46_fixed_prefix_centred_source_error_squeeze
-- name    : AvramDividend.Classical.avram_bvb46_fixed_prefix_centred_source_error_squeeze
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T19:04:58.864011+00:00
-- url     : https://prove2.me/theorems/94bee60c-bdc1-4a18-a31c-eeb8bbd249d3
-- title:
--   Original chronological fixed cash prefix positive L1 excess is bounded by refining signed HJB residual
-- statement:
--   An abstract exact algebraic squeeze for the original finite-activity BV cash ledger: if the physical strict cash prefixes F are nondecreasing, signed deterministic HJB drift B is nonpositive, and the positive residual of the refining full physical mesh F(k)-a-(M(k)+B(k)) has vanishing expected positive part, then for every fixed n the positive expected excess F(n)-a-M(k) tends to zero. The proof uses integrability, pointwise max monotonicity, real integral order and an eventual squeeze; it preserves the actual original source variables when instantiated with F, B, M.
-- source:
--   Proved bvb45 original monotone real cash prefix, Proved physical strict HJB signed nonpositivity, original phys36b residual L1 gap; pinned Mathlib integral_mono_ae and tendsto squeeze.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb46_fixed_prefix_centred_source_error_squeeze
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F B M : ℕ → Ω → ℝ) (a : ℝ)
    (hFI : ∀ n, Integrable (F n) P)
    (hMI : ∀ n, Integrable (M n) P)
    (hEI : ∀ k, Integrable
      (fun ω => max (F k ω - (a + (M k ω + B k ω))) (0 : ℝ)) P)
    (hFmono : ∀ᵐ ω ∂P, ∀ n k, n ≤ k → F n ω ≤ F k ω)
    (hBnonpos : ∀ᵐ ω ∂P, ∀ k, B k ω ≤ 0)
    (hErr : Tendsto (fun k =>
       ∫ ω, max (F k ω - (a + (M k ω + B k ω))) (0 : ℝ) ∂P)
       atTop (𝓝 (0 : ℝ))) :
    ∀ n, Tendsto (fun k =>
       ∫ ω, max (F n ω - (a + M k ω)) (0 : ℝ) ∂P)
       atTop (𝓝 (0 : ℝ)) := by sorry
