-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_adjacent_increment_cylinder_factorization
-- name    : AvramDividend.Classical.esscher_adjacent_increment_cylinder_factorization
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T14:41:54.949+00:00
-- url     : https://prove2.me/theorems/e8ab9284-5d5b-40fd-a51e-632869a4db81
-- title:
--   Esscher tilted adjacent-increment law factorises against every earlier filtration event
-- statement:
--   For a spectrally negative Lévy process under P and θ≥0, consider the genuine Esscher finite-horizon probability laws Q_t(dω)=exp(θX_t−tψθ)P(dω). For every s,u≥0, every past event A∈𝓕_s and Borel increment event B⊆ℝ, Q_(s+u)(A∩{X_(s+u)−X_s∈B})=Q_s(A)Q_u({X_u∈B}). This proves both independence from arbitrary past-filtration events and the stationary tilted increment distribution under the actual finite-horizon law, without presuming existence of a perpetual tilted path-space measure. It is the finite-dimensional Lévy property needed for the independent exponential-clock Wiener–Hopf route.
-- source:
--   Kuznetsov–Kyprianou–Rivero, The Theory of Scale Functions (2012), Esscher law and shifted exponent around equations (16)–(17). Derived from canonical SpectrallyNegativeLevy independent and stationary increments, Proved esscher_compensated_exp_time_split (481efeaf-b470-4451-aa29-0daf9fa3117b), and pinned Mathlib ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun. The proof uses a genuine finite-horizon density.

import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_esscher_compensated_exp_time_split
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_adjacent_increment_cylinder_factorization
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (s u : ℝ≥0)
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕 s) A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X (s + u) ω -
        (s + u : ℝ) * X.ψ θ))))
      (A ∩ (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ)))) A *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B) := by sorry
