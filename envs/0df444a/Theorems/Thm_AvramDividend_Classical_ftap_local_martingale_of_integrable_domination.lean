-- Prove2me | Theorems.Thm_AvramDividend_Classical_ftap_local_martingale_of_integrable_domination
-- name    : AvramDividend.Classical.ftap_local_martingale_of_integrable_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T10:54:27.692976+00:00
-- url     : https://prove2.me/theorems/4a68f8c4-579b-44c9-834e-b446d2412f51
-- title:
--   Integrably dominated local martingale is a true martingale (FTAP proof adaptation)
-- statement:
--   An adapted real-valued local martingale which is bounded almost surely for every time by one integrable random variable is a true martingale. Adaptation of the actual pathwise localisation and dominated-convergence proof by Mocho Go, lean-ftap-closedness at commit 8c9c46e1b6e455f7d3069062957d4363879836ce under Apache-2.0. In Avram this will justify centring after an original integrable path envelope has separately been proved; no envelope is asserted here.
-- source:
--   https://github.com/selpoG/lean-ftap-closedness/blob/8c9c46e1b6e455f7d3069062957d4363879836ce/FTAPTheorem42/Stochastic/Martingale/Basic/DominatedLocalMartingale.lean

import Mathlib
open Filter MeasureTheory Set
open scoped NNReal Topology

theorem AvramDividend.Classical.ftap_local_martingale_of_integrable_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 mΩ}
    {μ : Measure Ω} [SigmaFiniteFiltration μ ℱ]
    {X : ℝ≥0 → Ω → ℝ}
    (hX : ProbabilityTheory.Locally
      (fun Y : ℝ≥0 → Ω → ℝ => Martingale Y ℱ μ) ℱ X μ)
    (hAdapted : StronglyAdapted ℱ X)
    (Z : Ω → ℝ) (hZ : Integrable Z μ)
    (hdom : ∀ᵐ ω ∂μ, ∀ t, |X t ω| ≤ Z ω) :
    Martingale X ℱ μ := by sorry
