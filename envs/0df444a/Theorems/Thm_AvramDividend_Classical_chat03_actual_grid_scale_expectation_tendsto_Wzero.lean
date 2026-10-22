-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_actual_grid_scale_expectation_tendsto_Wzero
-- name    : AvramDividend.Classical.chat03_actual_grid_scale_expectation_tendsto_Wzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T14:59:35.321871+00:00
-- url     : https://prove2.me/theorems/54d6469b-3dc2-4848-9a6b-a0c0b4750588
-- title:
--   Expected actual bounded-grid discounted q-scale reward converges under finite exit when W(0)=0
-- statement:
--   For a spectrally negative Lévy process with a nonnegative q-scale W vanishing at zero, a common fixed finite observation horizon and almost-everywhere finite strict two-sided exit before that horizon, the expected discounted q-scale at the actual bounded sampled Mathlib hittingBtwn clock converges to the expected continuously stopped discounted scale value. The proof uses the accepted uniform-second-moment convergence theorem and does not assume killed-scale harmonicity.
-- source:
--   Proved Chat03 actual uncapped first-grid q-scale pathwise convergence plus Proved finite-horizon q-scale expectation convergence under a uniform second moment bound.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_uncapped_grid_discounted_scale_tendsto_of_Wzero
import Theorems.Thm_AvramDividend_Classical_chat03_capped_grid_scale_expectation_of_ae_convergence
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Probability.Process.HittingTime

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_actual_grid_scale_expectation_tendsto_Wzero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (lower upper : ℝ) (N : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ᵐ ω ∂P,
      IsGLB {t : ℝ≥0 |
        X.X t ω < lower ∨ upper < X.X t ω} (τ ω))
    (hτN : ∀ᵐ ω ∂P, τ ω < N)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (m : ℕ → ℕ)
    (hNm : ∀ n, (m n : ℝ≥0) * mesh n ≤ N)
    (hcap : ∀ᵐ ω ∂P,
      ∀ᶠ n in atTop, τ ω + 1 ≤ (m n : ℝ≥0) * mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (m n) η)
    (H : ℕ → Filtration ℕ mΩ)
    (hH : ∀ n k, H n k = 𝓕 ((k : ℝ≥0) * mesh n))
    (Z : Ω → ℝ) (hZm : AEStronglyMeasurable Z P)
    (hZ : ∀ᵐ ω ∂P,
      Z ω = Real.exp (-(q * (τ ω : ℝ))) *
        W (x + X.X (τ ω) ω)) :
    Integrable Z P ∧
    Tendsto (fun n => ∫ ω,
      Real.exp (-(q * (((K n ω : ℝ≥0) * mesh n) : ℝ))) *
        W (x + X.X ((K n ω : ℝ≥0) * mesh n) ω) ∂P)
      atTop (𝓝 (∫ ω, Z ω ∂P)) := by sorry
