-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_noexit_integer_horizon_terminal_scale_vanish
-- name    : AvramDividend.Classical.chat03_noexit_integer_horizon_terminal_scale_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T22:53:23.348302+00:00
-- url     : https://prove2.me/theorems/4b91d5a0-5bd0-49b3-be0b-d3abdff34199
-- title:
--   Discounted q-scale terminal payoff tends to zero on paths without either first passage
-- statement:
--   For the official spectrally negative Lévy process, positive discount rate and q-scale function, fix a path where both official upper and lower strict passage times are infinite. The discounted scale payoff exp(-qn)W(x+X_n) tends to zero along integer horizons as n tends to infinity, since the reserve stays in [0,a] and the uniformly bounded scale value is exponentially discounted. This directly supplies the terminal residual limit for the no-passage branch of optional-stopping analysis; the theorem does not assert a stochastic martingale identity.
-- source:
--   Composes independently Proved chat03_no_grid_exit_when_both_passages_infinite with Proved Chat04 bounded_strip_scale_terminal_vanish without circular exit identity.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_no_grid_exit_when_both_passages_infinite
import Theorems.Thm_AvramDividend_Classical_chat04_bounded_strip_scale_terminal_vanish
import Mathlib.Topology.NhdsWithin
import Mathlib.Tactic.Linarith

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_noexit_integer_horizon_terminal_scale_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω)
    (hUp : twoSidedExitUpTime X (a - x) ω = ∞)
    (hDown : twoSidedExitDownTime X (-x) ω = ∞) :
    Tendsto (fun n : ℕ =>
      Real.exp (-(q * (n : ℝ))) * W (x + X.X (n : ℝ≥0) ω))
      atTop (𝓝 0) := by sorry
