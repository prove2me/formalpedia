-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_hjb_finite_dividend_telescoping
-- name    : AvramDividend.Classical.local_verification_hjb_finite_dividend_telescoping
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T14:41:08.883649+00:00
-- url     : https://prove2.me/theorems/a7b8173d-98a3-4a01-a7db-ed2b67ae33b3
-- title:
--   The HJB dividend inequality telescopes over any finite sequence of solvency-preserving payments
-- statement:
--   For a verification function satisfying the HJB smoothness and gradient inequality, consider a discrete sequence of reserve states u_k and nonnegative dividend payments d_k, satisfying u_(k+1)=u_k−d_k, 0≤d_k≤u_k and ENNReal.ofReal(u_k)≤C. Then the sum of the first n payments is at most w(u_0)−w(u_n). The previously Proved generic HJB secant gives d_k≤w(u_k)−w(u_(k+1)) at each step. Sum these inequalities with induction and telescoping. This finite partition payment inequality is a legitimate deterministic ingredient for the controlled finite-variation dividend component, even with multiple atoms. It does not claim a stochastic martingale or allow changes in the uncontrolled Lévy reserve between payments without an additional process-drift estimate.
-- source:
--   Only Proved local_verification_hjb_controls_dividend_jump_le_cap, Finset.sum_range_succ and arithmetic; no pending imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_controls_dividend_jump_le_cap

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_hjb_finite_dividend_telescoping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (u d : ℕ → ℝ)
    (hupdate : ∀ k : ℕ, u (k + 1) = u k - d k)
    (hpos : ∀ k : ℕ, 0 ≤ d k)
    (hsolv : ∀ k : ℕ, d k ≤ u k)
    (hcap : ∀ k : ℕ, ENNReal.ofReal (u k) ≤ C)
    (n : ℕ) :
    (∑ k ∈ Finset.range n, d k) ≤ w (u 0) - w (u n) := by sorry
