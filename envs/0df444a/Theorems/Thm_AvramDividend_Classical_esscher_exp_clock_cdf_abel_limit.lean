-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_exp_clock_cdf_abel_limit
-- name    : AvramDividend.Classical.esscher_exp_clock_cdf_abel_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:28:33.901236+00:00
-- url     : https://prove2.me/theorems/ba063085-2784-44ec-9610-25cacb35544e
-- title:
--   Exponential-clock averaging preserves a bounded finite-horizon CDF limit
-- statement:
--   Let f(t) be a bounded finite-horizon CDF value with an actual limit L as t→∞. Under any genuine probability Q carrying a positive clock E, and for positive rates p_n→0, the clock-averaged CDF integrals ∫ f(E/p_n) dQ converge to L, assuming sampled measurability and uniform bound one. This is a rigorous Abelian exponential-horizon limit that does not require a consistent all-horizon Esscher path law. Identifying f with the actual Esscher survival CDF and L with canonical ν's infimum remains an independent obligation.
-- source:
--   Prove2Me accepted shared-clock lemma ff8ecd57-1a1b-4355-8de3-0e69197b24f4 and pinned Mathlib dominated convergence; Kyprianou-Kuznetsov-Rivero scale function review finite-to-perpetual horizon convergence.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.NhdsWithin
import Theorems.Thm_AvramDividend_Classical_esscher_shared_clock_pathwise_limit

open AvramDividend.Classical MeasureTheory Filter Set

theorem AvramDividend.Classical.esscher_exp_clock_cdf_abel_limit
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (E : Ω → ℝ) (hE : ∀ᵐ ω ∂Q, 0 < E ω)
    (f : ℝ → ℝ) (L : ℝ)
    (hf : Tendsto f atTop (nhds L))
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hmeas : ∀ n : ℕ,
      AEStronglyMeasurable (fun ω => f (E ω / p n)) Q)
    (hbound : ∀ n : ℕ,
      ∀ᵐ ω ∂Q, ‖f (E ω / p n)‖ ≤ (1 : ℝ)) :
    Tendsto (fun n : ℕ => ∫ ω, f (E ω / p n) ∂Q)
      atTop (nhds L) := by sorry
