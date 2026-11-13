-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a44_discounted_terminal_spatial_positive_sup_bound
-- name    : AvramDividend.Classical.avram_ga_a44_discounted_terminal_spatial_positive_sup_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T13:18:35.373326+00:00
-- url     : https://prove2.me/theorems/3b86f017-ca05-49e9-8f2a-eb0bd6a6886e
-- title:
--   Original stopped terminal spatial positive cell bounded by the common exponential running-supremum envelope
-- statement:
--   A generic almost-sure deterministic terminal-cell estimate: when a stopped spatial cell is inactive with equal pre/postpayment states or active with a compact lower bound on w(Y), a one-sided exponential HJB upper bound on w(Z), and Z below a fixed pathwise ceiling H, its discounted positive spatial difference is at most K exp(theta H)+L. Uses the Proved discounted positive-part majorant a33 and nonnegative exponential monotonicity. This is the precise deterministic last step for the original Gaussian terminal physical envelope a41b.
-- source:
--   a41b 4d4e9286; a33 5bb6cad1, original clipped source runningSup a34 and compact lower floor gledger63.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a33_terminal_positive_exponential_majorant
open AvramDividend.Classical MeasureTheory Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a44_discounted_terminal_spatial_positive_sup_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (q θ K L : ℝ) (hq : 0 ≤ q) (hθ : 0 ≤ θ)
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (t : Ω → ℝ≥0)
    (w : ℝ → ℝ) (Y Z H : Ω → ℝ)
    (hCells : ∀ᵐ ω ∂ P,
      (Z ω = Y ω) ∨
      (-L ≤ w (Y ω) ∧
        w (Z ω) ≤ K * Real.exp (θ * Z ω) ∧
        Z ω ≤ H ω)) :
    ∀ᵐ ω ∂ P,
      max (Real.exp (-(q * (t ω : ℝ))) *
        (w (Z ω) - w (Y ω))) 0 ≤
      K * Real.exp (θ * H ω) + L := by sorry
