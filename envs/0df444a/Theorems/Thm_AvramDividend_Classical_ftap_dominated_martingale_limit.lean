-- Prove2me | Theorems.Thm_AvramDividend_Classical_ftap_dominated_martingale_limit
-- name    : AvramDividend.Classical.ftap_dominated_martingale_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T10:55:56.120229+00:00
-- url     : https://prove2.me/theorems/881fe49b-1455-4818-9650-5080abac17cf
-- title:
--   Domination allows martingale convergence through almost-everywhere limits (FTAP argument)
-- statement:
--   Given a strongly adapted real process, a sequence of true martingale processes converging almost everywhere at each time, a single integrable dominating random variable bounding the sequence and original process, conclude the limit is a true martingale. Adapted from Mocho Go, FTAPTheorem42/Stochastic/Martingale/Basic/DominatedLocalMartingale.lean at commit 8c9c46e1b6e455f7d3069062957d4363879836ce (Apache-2.0). It will be applied to localising stopped processes to prove the parent theorem 4a68f8c4-579b-44c9-834e-b446d2412f51 without assuming its conclusion.
-- source:
--   https://github.com/selpoG/lean-ftap-closedness/blob/8c9c46e1b6e455f7d3069062957d4363879836ce/FTAPTheorem42/Stochastic/Martingale/Basic/DominatedLocalMartingale.lean

import Mathlib
open Filter MeasureTheory Set
open scoped NNReal Topology

theorem AvramDividend.Classical.ftap_dominated_martingale_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 mΩ}
    {μ : Measure Ω} [SigmaFiniteFiltration μ ℱ]
    (X : ℝ≥0 → Ω → ℝ)
    (Y : ℕ → ℝ≥0 → Ω → ℝ)
    (hAdapted : StronglyAdapted ℱ X)
    (hYn : ∀ n, Martingale (Y n) ℱ μ)
    (Z : Ω → ℝ) (hZ : Integrable Z μ)
    (hdomX : ∀ᵐ ω ∂μ, ∀ t, |X t ω| ≤ Z ω)
    (hYdom : ∀ n t, ∀ᵐ ω ∂μ, ‖Y n t ω‖ ≤ Z ω)
    (hYlim : ∀ t, ∀ᵐ ω ∂μ,
      Tendsto (fun n => Y n t ω) atTop (𝓝 (X t ω))) :
    Martingale X ℱ μ := by sorry
