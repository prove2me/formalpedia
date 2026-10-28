-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_partial_sum_aestronglymeasurable
-- name    : AvramDividend.Classical.causal_neumann_partial_sum_aestronglymeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T21:14:19.877982+00:00
-- url     : https://prove2.me/theorems/8019bf24-a877-457e-89dd-ec820fc53822
-- title:
--   Finite Neumann convolution sums are ae strongly measurable from term integrability
-- statement:
--   The hMeas hypothesis in the Gaussian causal Neumann dominated-convergence theorem follows automatically from its existing individual convolution integrability assumptions hI. Thus finite-sum measurability introduces no additional analytic condition.
-- source:
--   Each term-integrability hypothesis hI already gives ae strong measurability of the corresponding kernel product on volume.restrict(Ioc(0,x)). Apply the Mathlib Finset.aestronglyMeasurable_fun_sum lemma, then distribute the common kernel factor over the finite pointwise Neumann sum. The exact conclusion is hMeas required by the Proved causal_neumann_resolvent_dominated_convergence theorem.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Algebra.BigOperators.Pi

open MeasureTheory Set

theorem AvramDividend.Classical.causal_neumann_partial_sum_aestronglymeasurable
    (B : ℝ → ℝ) (Q : ℕ → ℝ → ℝ)
    (hI : ∀ m : ℕ, ∀ x : ℝ, ∀ i ∈ Finset.range (m + 1),
      IntegrableOn (fun s : ℝ => B (x - s) * Q i s)
        (Ioc (0 : ℝ) x) volume) :
    ∀ x : ℝ, ∀ n : ℕ, AEStronglyMeasurable
      (fun s : ℝ => B (x - s) * (∑ i ∈ Finset.range (n + 1), Q i) s)
      (volume.restrict (Ioc (0 : ℝ) x)) := by sorry
