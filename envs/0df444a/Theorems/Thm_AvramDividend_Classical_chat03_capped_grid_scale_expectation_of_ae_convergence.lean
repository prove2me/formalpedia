-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_capped_grid_scale_expectation_of_ae_convergence
-- name    : AvramDividend.Classical.chat03_capped_grid_scale_expectation_of_ae_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:48:16.534004+00:00
-- url     : https://prove2.me/theorems/7a600173-d2db-4610-b345-100a852c3e55
-- title:
--   Finite-grid stopped q-scale expectation converges under pathwise convergence and a common time horizon
-- statement:
--   For a genuine spectrally negative Lévy process with a canonical nonnegative q-scale function and a common finite time horizon, consider first strict two-sided grid exits on any sequence of monotone deterministic grids with matching sampled filtrations. If the discounted stopped q-scale values converge almost everywhere to a strongly measurable random payoff Z, then Z is integrable and their expectations converge to the expectation of Z. Nonnegativity, stopped-payoff measurability and the mesh-uniform squared-moment bound follow from the process and scale-function assumptions and previously accepted Chat 03 theorems. The theorem makes no harmonicity or optional-stopping assumption.
-- source:
--   Derived from Proved Chat03 actual bounded-grid L² theorem d591a684-7fbc-4f11-9c18-7d38c35320a0 and Proved uniform second moment expectation convergence bef79c38-a4aa-42be-b897-fd1baeed7998.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_grid_stopped_reserve_time_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_bounded_grid_l2_unconditional
import Theorems.Thm_AvramDividend_Classical_nonnegative_integral_tendsto_of_uniform_second_moment
import Mathlib.Probability.Process.HittingTime

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.chat03_capped_grid_scale_expectation_of_ae_convergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (clock : ℕ → ℕ → ℝ≥0)
    (hc : ∀ n, Monotone (clock n))
    (hc0 : ∀ n, clock n 0 = 0)
    (H : ℕ → Filtration ℕ mΩ)
    (hH : ∀ n k, H n k = 𝓕 (clock n k))
    (lower upper : ℝ) (m : ℕ → ℕ) (K : ℕ → Ω → ℕ)
    (hK : ∀ n ω, K n ω = hittingBtwn
      (fun k ω => max (X.X (clock n k) ω - upper)
        (lower - X.X (clock n k) ω)) (Set.Ioi (0 : ℝ)) 0 (m n) ω)
    (N : ℝ≥0) (hNm : ∀ n, clock n (m n) ≤ N)
    (Z : Ω → ℝ) (hZm : AEStronglyMeasurable Z P)
    (hconv : ∀ᵐ ω ∂P,
      Tendsto (fun n => Real.exp (-(q * (clock n (K n ω) : ℝ))) *
        W (x + X.X (clock n (K n ω)) ω)) atTop (𝓝 (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω,
        Real.exp (-(q * (clock n (K n ω) : ℝ))) *
          W (x + X.X (clock n (K n ω)) ω) ∂P)
        atTop (𝓝 (∫ ω, Z ω ∂P)) := by sorry
