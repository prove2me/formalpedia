-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_shared_clock_sequential_laplace_limit
-- name    : AvramDividend.Classical.esscher_shared_clock_sequential_laplace_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T16:17:21.716183+00:00
-- url     : https://prove2.me/theorems/fb13cec9-4e02-4393-8b99-5178b2197fcb
-- title:
--   Bounded Laplace convergence along coupled exponential-clock rate sequences
-- statement:
--   On one genuine finite probability law Q, a shared strictly positive clock E and a path observable Y_t tending almost surely to a finite Y∞ imply bounded Laplace expectation convergence at random horizons E/p_n for every positive rate sequence p_n→0. Measurability and nonnegativity of the sampled magnitudes are explicit assumptions. This assembles the canonically Proved shared-clock pathwise lemma and bounded-convergence lemma without inventing an Esscher process law.
-- source:
--   Prove2Me accepted shared-clock pathwise limit ff8ecd57-1a1b-4355-8de3-0e69197b24f4 and bounded Laplace dominated convergence 03cb3060-8804-45aa-987a-004a04a0605a; Kyprianou scale-functions review exponential horizons.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.NhdsWithin
import Theorems.Thm_AvramDividend_Classical_esscher_shared_clock_pathwise_limit
import Theorems.Thm_AvramDividend_Classical_esscher_infimum_bounded_laplace_convergence

open AvramDividend.Classical MeasureTheory Filter Set

theorem AvramDividend.Classical.esscher_shared_clock_sequential_laplace_limit
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsFiniteMeasure Q]
    (E : Ω → ℝ) (Y : ℝ → Ω → ℝ) (Yinf : Ω → ℝ)
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hE : ∀ᵐ ω ∂Q, 0 < E ω)
    (hY : ∀ᵐ ω ∂Q,
      Tendsto (fun t : ℝ => Y t ω) atTop (nhds (Yinf ω)))
    (β : ℝ) (hβ : 0 < β)
    (hmeas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun ω => Real.exp (-β * Y (E ω / p n) ω)) Q)
    (hpos : ∀ n : ℕ, ∀ᵐ ω ∂Q, 0 ≤ Y (E ω / p n) ω) :
    Tendsto
      (fun n : ℕ => ∫ ω, Real.exp (-β * Y (E ω / p n) ω) ∂Q)
      atTop
      (nhds (∫ ω, Real.exp (-β * Yinf ω) ∂Q)) := by sorry
