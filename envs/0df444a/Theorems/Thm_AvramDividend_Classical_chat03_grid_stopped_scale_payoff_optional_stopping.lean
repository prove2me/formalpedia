-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_grid_stopped_scale_payoff_optional_stopping
-- name    : AvramDividend.Classical.chat03_grid_stopped_scale_payoff_optional_stopping
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-21T04:46:57.209779+00:00
-- url     : https://prove2.me/theorems/ee165062-110d-4b4e-8683-6f57c532819d
-- title:
--   Bounded optional stopping of the q-scale payoff at the first strict two-sided grid exit
-- statement:
--   Let X be a spectrally negative Levy process, q > 0, W its q-scale function with W(0) = 0, and sample the process on a deterministic increasing clock. Stop the discounted q-scale payoff at the first sampled time at which the reserve leaves the interval (lower, upper). The expected stopped payoff equals the initial scale value. The mechanism is optional stopping of the discounted q-scale payoff, which is a martingale by the q-scale semigroup harmonicity. This is the discrete step from which the continuous-time two-sided exit identity follows by passing to the limit on increasingly fine meshes, the stopped payoff converging to the continuous one because the scale function is continuous and the grid exit infimum converges to the continuous passage infimum.
-- source:
--   Bounded optional stopping of the q-scale payoff at a strict two-sided grid exit, the discrete counterpart of the two-sided exit identity of Avram, Palmowski and Pistorius (2007), equation (3.6). The optional-stopping mechanism is the Proved theorem chat03_two_sided_grid_stopped_martingale_identity, and the martingale property of the discounted q-scale payoff follows from the q-scale semigroup harmonicity. Formalised in the Avram Dividend Classical proof programme.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat03_grid_stopped_scale_payoff_optional_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) (hc0 : clock 0 = 0)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (lower upper : ℝ) (m : ℕ)
    (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Set.Ioi (0 : ℝ)) 0 m ω) :
    (∫⁻ ω,
      if X.X (clock (K ω)) ω < lower then 0 else
        ENNReal.ofReal
          (Real.exp (-(q * (clock (K ω) : ℝ))) *
            W (x + X.X (clock (K ω)) ω)) ∂P) =
      ENNReal.ofReal (W x) := by sorry
