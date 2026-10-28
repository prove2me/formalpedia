-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_terminal_increment_cylinder_factorization
-- name    : AvramDividend.Classical.esscher_terminal_increment_cylinder_factorization
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T15:06:19.889342+00:00
-- url     : https://prove2.me/theorems/b4c43ae0-cb9d-43f3-bb6c-e484166ddf0e
-- title:
--   Esscher stationary independent increment cylinders persist under every later terminal law
-- statement:
--   For θ≥0, s,u,T≥0 and s+u≤T, every event A in the filtration at s and Borel increment event B, the terminal-T Esscher probability of A and the increment X_(s+u)−X_s in B is Q_s(A)Q_u(X_u in B). The theorem gives the finite-horizon stationary independent-increments cylinder law under every later tilted law.
-- source:
--   Kuznetsov–Kyprianou–Rivero, The Theory of Scale Functions (2012), §2.1; Prove2Me accepted theorems esscher_adjacent_increment_cylinder_factorization e8ab9284-5d5b-40fd-a51e-632869a4db81 and chat04_esscher_finite_horizon_laws_consistent_on_past_events a74b3334-5c28-44d1-ae88-3057d26957f4.

import Theorems.Thm_AvramDividend_Classical_esscher_adjacent_increment_cylinder_factorization
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_terminal_increment_cylinder_factorization
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (s u T : ℝ≥0) (hT : s + u ≤ T)
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕 s) A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
      (A ∩ (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ)))) A *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B) := by sorry
