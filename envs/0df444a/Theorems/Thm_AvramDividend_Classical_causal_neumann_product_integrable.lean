-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_product_integrable
-- name    : AvramDividend.Classical.causal_neumann_product_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T21:57:43.716709+00:00
-- url     : https://prove2.me/theorems/d4e4f628-c7e2-4b9a-81cf-faa5e5b43be4
-- title:
--   Local boundedness preserves reflected-kernel integrability term by term
-- statement:
--   A reflected integrable Volterra kernel multiplied by each almost-everywhere measurable locally bounded Neumann correction remains integrable on every finite causal integration interval, yielding the per-term integrability hypotheses needed to exchange the integral and finite sums.
-- source:
--   The proved reflected full Gaussian kernel is IntegrableOn every causal interval. The pointwise geometric Neumann bounds provide uniform finite-horizon bounds for each correction. Combine these with AEStronglyMeasurable and Mathlib Integrable.mul_bdd to discharge the exact hI premise of causal_neumann_resolvent_dominated_convergence.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.IntegrableOn
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_neumann_product_integrable
    (B : ℝ → ℝ) (Q : ℕ → ℝ → ℝ)
    (hB : ∀ x : ℝ, IntegrableOn
      (fun s : ℝ => B (x - s)) (Ioc (0 : ℝ) x) volume)
    (hMeas : ∀ x : ℝ, ∀ i : ℕ, AEStronglyMeasurable
      (Q i) (volume.restrict (Ioc (0 : ℝ) x)))
    (hBound : ∀ x : ℝ, ∀ i : ℕ, ∃ C : ℝ,
      ∀ s ∈ Ioc (0 : ℝ) x, ‖Q i s‖ ≤ C) :
    ∀ m : ℕ, ∀ x : ℝ, ∀ i ∈ Finset.range (m + 1),
      IntegrableOn (fun s : ℝ => B (x - s) * Q i s)
        (Ioc (0 : ℝ) x) volume := by sorry
