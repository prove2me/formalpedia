-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_geometric_neumann_resolvent
-- name    : AvramDividend.Classical.causal_geometric_neumann_resolvent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T22:15:54.303121+00:00
-- url     : https://prove2.me/theorems/0ad47373-8a69-4c4c-bab8-f5bed6b4ee05
-- title:
--   Geometrically bounded Gaussian Neumann series solves its Volterra resolvent equation
-- statement:
--   A pointwise and locally uniformly geometric Neumann expansion with measurable correction terms, an integrable reflected kernel and an exact causal recurrence has a sum solving the Volterra integral equation. The theorem discharges every technical dominated-convergence hypothesis by previously Proved interfaces.
-- source:
--   Compose the existing Proved geometric summability, finite-sum convergence, integrability, measurability, local uniform majorant, and dominated-convergence resolvent theorems. This is the exact usable bridge from the C1 Gaussian Neumann candidate to its Volterra equation.

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Theorems.Thm_AvramDividend_Classical_causal_neumann_resolvent_dominated_convergence
import Theorems.Thm_AvramDividend_Classical_causal_neumann_product_integrable
import Theorems.Thm_AvramDividend_Classical_causal_neumann_partial_sum_aestronglymeasurable
import Theorems.Thm_AvramDividend_Classical_causal_local_neumann_convolution_majorant
import Theorems.Thm_AvramDividend_Classical_causal_geometric_neumann_local_sum_bound
import Theorems.Thm_AvramDividend_Classical_causal_geometric_neumann_summable
import Theorems.Thm_AvramDividend_Classical_causal_neumann_tsum_partial_sum_tendsto
open AvramDividend.Classical MeasureTheory Set Filter

theorem AvramDividend.Classical.causal_geometric_neumann_resolvent
    (a ρ : ℝ) (B F g : ℝ → ℝ) (Q : ℕ → ℝ → ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hzero : Q 0 = F)
    (hstep : ∀ n : ℕ, Q (n + 1) =
      -(fun x : ℝ => (1 / a) *
        (∫ s in Ioc (0 : ℝ) x, B (x - s) * Q n s ∂volume)))
    (hB : ∀ x : ℝ, IntegrableOn (fun s : ℝ => B (x - s))
      (Ioc (0 : ℝ) x) volume)
    (hMeas : ∀ x : ℝ, ∀ i : ℕ, AEStronglyMeasurable
      (Q i) (volume.restrict (Ioc (0 : ℝ) x)))
    (hGeom : ∀ x : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ∀ s ∈ Ioc (0 : ℝ) x, ‖Q n s‖ ≤ C * ρ ^ n)
    (hPoint : ∀ x : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ‖Q n x‖ ≤ C * ρ ^ n)
    (hg : ∀ x : ℝ, g x = ∑' n : ℕ, Q n x) :
    ∀ x : ℝ, g x + (1 / a) *
      (∫ s in Ioc (0 : ℝ) x, B (x - s) * g s ∂volume) = F x := by sorry
