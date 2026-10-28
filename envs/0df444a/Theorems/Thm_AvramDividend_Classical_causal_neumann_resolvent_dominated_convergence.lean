-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_neumann_resolvent_dominated_convergence
-- name    : AvramDividend.Classical.causal_neumann_resolvent_dominated_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T14:28:31.008243+00:00
-- url     : https://prove2.me/theorems/50dd5316-2aad-47d4-bd56-997f816a5c1e
-- title:
--   Neumann causal Volterra resolvent from geometric domination and pointwise convergence
-- statement:
--   A Neumann sequence obeying the exact causal Volterra recursion solves the integral resolvent equation at its pointwise limit if the remainder tends to zero and the partial-sum kernel products admit a common integrable majorant. Measurability and majorisation ensure convergence of the convolution integrals by dominated convergence, discharging the analytic hTS condition in the existing infinite Neumann lemma.
-- source:
--   Combine dominated convergence of the actual causal integral with the Proved finite-to-infinite Neumann resolvent telescope.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Theorems.Thm_AvramDividend_Classical_causal_neumann_integral_resolvent_of_convergence
import Theorems.Thm_AvramDividend_Classical_causal_Ioc_kernel_integral_tendsto_dominated

open AvramDividend.Classical MeasureTheory Set Filter

theorem AvramDividend.Classical.causal_neumann_resolvent_dominated_convergence
    (a : ℝ) (B F g : ℝ → ℝ) (Q : ℕ → ℝ → ℝ)
    (hzero : Q 0 = F)
    (hstep : ∀ n : ℕ, Q (n + 1) =
      -(fun x : ℝ => (1 / a) *
        (∫ s in Ioc (0 : ℝ) x, B (x - s) * Q n s ∂volume)))
    (hI : ∀ m : ℕ, ∀ x : ℝ, ∀ i ∈ Finset.range (m + 1),
      IntegrableOn (fun s : ℝ => B (x - s) * Q i s)
        (Ioc (0 : ℝ) x) volume)
    (hS : ∀ x : ℝ, Tendsto
      (fun n : ℕ => (∑ i ∈ Finset.range (n + 1), Q i) x)
      atTop (nhds (g x)))
    (hQ : ∀ x : ℝ, Tendsto (fun n : ℕ => Q (n + 1) x)
      atTop (nhds (0 : ℝ)))
    (hMeas : ∀ x : ℝ, ∀ n : ℕ, AEStronglyMeasurable
      (fun s : ℝ => B (x - s) * (∑ i ∈ Finset.range (n + 1), Q i) s)
      (volume.restrict (Ioc (0 : ℝ) x)))
    (hDom : ∀ x : ℝ, ∃ D : ℝ → ℝ,
      IntegrableOn D (Ioc (0 : ℝ) x) volume ∧
      (∀ n : ℕ, ∀ᵐ s ∂(volume.restrict (Ioc (0 : ℝ) x)),
        ‖B (x - s) * (∑ i ∈ Finset.range (n + 1), Q i) s‖ ≤ D s)) :
    ∀ x : ℝ, g x + (1 / a) *
      (∫ s in Ioc (0 : ℝ) x, B (x - s) * g s ∂volume) = F x := by sorry
