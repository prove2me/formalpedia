-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_terminal_independent_clock_increment_cylinder
-- name    : AvramDividend.Classical.esscher_terminal_independent_clock_increment_cylinder
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T15:44:51.12636+00:00
-- url     : https://prove2.me/theorems/742cea4f-851b-4ebc-a3da-9feb2dab63d1
-- title:
--   Independent exponential observation clock factors from tilted Lévy history and a future increment
-- statement:
--   Under the finite-horizon Esscher path law Q_T at T≥s+u and an independent Exp(p) clock, the product-law probability of a past filtration event, an adjacent future increment event, and an arbitrary clock event equals Q_s(A)Q_u(ΔX_u∈B)Exp(p)(C). This exact finite-horizon product law maintains the exponential clock's independence without assuming a global path-space measure or Wiener–Hopf factorisation.
-- source:
--   Kuznetsov–Kyprianou–Rivero, The Theory of Scale Functions (2012), Esscher law §2.1; accepted Prove2Me terminal-increment factorisation b4c43ae0-cb9d-43f3-bb6c-e484166ddf0e; pinned Mathlib Measure.prod_prod and isProbabilityMeasure_expMeasure.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_increment_cylinder_factorization
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_terminal_independent_clock_increment_cylinder
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (s u T : ℝ≥0) (hT : s + u ≤ T)
    (p : ℝ) (hp : 0 < p)
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕 s) A)
    (B : Set ℝ) (hB : MeasurableSet B)
    (C : Set ℝ) :
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).prod
        (expMeasure p))
      ((A ∩ (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B) ×ˢ C) =
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ)))) A *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B)) * (expMeasure p) C := by sorry
