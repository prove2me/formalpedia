-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_monotone_centered_excess_budget
-- name    : AvramDividend.Classical.avram_bva_a22_monotone_centered_excess_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T22:57:52.113114+00:00
-- url     : https://prove2.me/theorems/b8328cdb-a415-4d58-9993-94f559aea39d
-- title:
--   Centred compensated excess with vanishing positive mean bounds all monotone cash horizons
-- statement:
--   A probability-measure version of the diagonal positive-excess transfer. For integrable cash F_m and centred signed compensated noise N_m, if E[F_m] is nondecreasing and the L1 positive compensated excess E[(F_m-c-N_m)^+] tends to zero, then every E[F_k] is at most c. This connects the cofinal diagonal stochastic route to original finite-horizon verification without asserting an arbitrary-band pointwise pathwise chain rule.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_monotone_centered_excess_budget
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F N : ℕ → Ω → ℝ) (c : ℝ)
    (hF : ∀ m, Integrable (F m) P)
    (hN : ∀ m, Integrable (N m) P)
    (hNzero : ∀ m, (∫ ω, N m ω ∂P) = 0)
    (hMono : Monotone (fun m => ∫ ω, F m ω ∂P))
    (hExcess : Tendsto
      (fun m => ∫ ω, max (F m ω - (c + N m ω)) 0 ∂P)
      atTop (𝓝 (0 : ℝ))) :
    ∀ k : ℕ, (∫ ω, F k ω ∂P) ≤ c := by sorry
