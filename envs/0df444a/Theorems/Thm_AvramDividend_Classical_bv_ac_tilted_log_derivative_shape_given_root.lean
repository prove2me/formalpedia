-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_ac_tilted_log_derivative_shape_given_root
-- name    : AvramDividend.Classical.bv_ac_tilted_log_derivative_shape_given_root
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T09:13:59.033577+00:00
-- url     : https://prove2.me/theorems/f45c2858-7fd7-49a8-b7a9-216cac5834b4
-- title:
--   Positive decreasing logarithmic derivative for the BV Esscher-tilted scale function
-- statement:
--   With positive root phi and BV AC Lévy law, the tilted scale function V=e^{-phi x}W(x) is positive on x>0 and has a continuous nonnegative nonincreasing logarithmic derivative g=V'/V on (0,infinity), with g(x)→0 as x→infinity. This is the exact analytic fluctuation-theory shape input needed to reconstruct an atomless excursion-height measure without a local-time formalisation. The reconstruction and integrated exponential identity are separate generically provable lemmas. This remains a substantial stochastic/renewal theorem, not implied by monotonicity of V alone.
-- source:
--   Chan–Kyprianou–Savov (2011), excursion representation (5),(6) and Esscher transform; Kuznetsov–Kyprianou–Rivero (2012), eqs. (2.17)-(2.19); alternative renewal/Stieltjes proof programme.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.bv_ac_tilted_log_derivative_shape_given_root
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ (V g : ℝ → ℝ),
      (∀ x : ℝ, 0 < x → 0 < V x) ∧
      ContinuousOn g (Ioi (0 : ℝ)) ∧
      AntitoneOn g (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, 0 < x → 0 ≤ g x) ∧
      Tendsto g atTop (𝓝 (0 : ℝ)) ∧
      (∀ x : ℝ, 0 < x → W x = Real.exp (φ * x) * V x) ∧
      (∀ x : ℝ, 0 < x → HasDerivAt V (V x * g x) x) := by sorry
