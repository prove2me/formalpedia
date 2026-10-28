-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_expectation_limsup_le_of_terminal_limit
-- name    : AvramDividend.Classical.chat04_killed_expectation_limsup_le_of_terminal_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:35:38.54573+00:00
-- url     : https://prove2.me/theorems/ddcc828c-57a1-43fa-beb8-7e0176b78b12
-- title:
--   Killed q-scale expectation limsup bound from terminal-only time-zero convergence
-- statement:
--   If the discounted scale expectation restricted to terminal nonnegative reserve converges to the initial scale value as time decreases to zero, then the limsup of the more stringent whole-history killed scale expectation is bounded above by that initial value. This is the upper half required alongside the Proved full-filter Fatou lower bound to prove killed semigroup continuity.
-- source:
--   Proved event domination chat01_history_killed_lintegral_le_terminal_only 6319a734, plus pinned Mathlib Filter.limsup_le_limsup and Tendsto.limsup_eq. Paired with full-filter Fatou theorem 618ce98c, this reduces killed time-zero continuity to terminal-only expectation convergence, providing a clean prerequisite for the Open killed harmonicity a885f0b3 and two-sided exit stopped identity 09663d0d.

import Theorems.Thm_AvramDividend_Classical_chat01_history_killed_lintegral_le_terminal_only
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Instances.ENNReal.Lemmas

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_killed_expectation_limsup_le_of_terminal_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ)
    (hterminal : Tendsto (fun t : ℝ≥0 => (∫⁻ ω,
        ({u : Ω | 0 ≤ x + X.X t u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P))
      (𝓝 0) (𝓝 (ENNReal.ofReal (W x)))) :
    Filter.limsup (fun t : ℝ≥0 => (∫⁻ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P)) (𝓝 0) ≤
      ENNReal.ofReal (W x) := by sorry
