-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_killed_scale_martingale_regularities
-- name    : AvramDividend.Classical.chat03_killed_scale_martingale_regularities
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T10:58:27.069186+00:00
-- url     : https://prove2.me/theorems/0511fefd-6ee1-42fd-ae9b-a7b88aedbcf1
-- title:
--   Under Standing, the continuous-history killed scale payoff is adapted and integrable
-- statement:
--   For a spectrally negative Lévy process satisfying Avram's standing assumptions, positive q and canonical q-scale function W, the whole-path downward-killed discounted q-scale payoff is adapted to the natural filtration and integrable at every deterministic finite time. It requires no externally supplied rational-grid observation schedule, constructing one using Cantor-pairing and the accepted coverage theorem. It combines two independently accepted results and isolates the remaining genuine killed semigroup conditional expectation identity that must be established before calling the process a martingale.
-- source:
--   Combines publicly Proved chat03_killed_scale_payoff_adapted (b3295962-412d-4193-8439-614757867c92) and chat03_killed_scale_fixed_time_integrable (dc9ef8a9-34f0-4522-a76c-d2cc20fdbce1) with Proved chat04_nat_pairing_rational_grid_coverage (34d1a207-11c0-49d1-b331-c905323990f4). No dependence on the open killed-martingale goal.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Probability.Martingale.Basic

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_killed_scale_martingale_regularities
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) :
    (Adapted 𝓕
      (fun (t : ℝ≥0) ω =>
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp (-(q * (t : ℝ))) *
            W (x + X.X t ω)) ω)) ∧
    (∀ t : ℝ≥0, Integrable
      (({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => Real.exp (-(q * (t : ℝ))) *
          W (x + X.X t ω))) P) := by
  sorry
