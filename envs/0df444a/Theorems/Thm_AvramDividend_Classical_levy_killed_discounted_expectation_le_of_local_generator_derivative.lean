-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_killed_discounted_expectation_le_of_local_generator_derivative
-- name    : AvramDividend.Classical.levy_killed_discounted_expectation_le_of_local_generator_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:18:28.587352+00:00
-- url     : https://prove2.me/theorems/c17f0209-3f25-43f9-99f5-8cd31b0a4b28
-- title:
--   Stopped/killed Lévy HJB semigroup domination from local generator derivative
-- statement:
--   Suppose f is the expectation of a reward w(z_s) only while a sample path is active, with the killed reward and killed generator integrable and differentiation under the expectation justified. It suffices to assume Gamma w(z_s) <= q w(z_s) on the active sample paths; no global generator inequality at ruined or out-of-range reserves is needed. The discounted killed reward exp(-qt) f(t) is then bounded by f(0). This is the local HJB counterpart of the previously Proved global semigroup bridge, and cleanly isolates the killed Dynkin/Ito derivative identity required for bounded- and unbounded-variation stochastic verification.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), local HJB verification with stopping and killing in Section 5.4.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_discounted_semigroup_le_initial_of_deriv_le

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_killed_discounted_expectation_le_of_local_generator_derivative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (q : ℝ) (z : ℝ → Ω → ℝ)
    (active : ℝ → Ω → Bool) (f : ℝ → ℝ)
    (hfcont : ContinuousOn f (Ici 0))
    (hfdiff : ∀ s : ℝ, 0 < s → DifferentiableAt ℝ f s)
    (hftrans : ∀ s : ℝ, 0 < s →
      f s = ∫ ω, if active s ω then w (z s ω) else 0 ∂P)
    (hfderiv : ∀ s : ℝ, 0 < s →
      deriv f s = ∫ ω,
        if active s ω then X.generator w (z s ω) else 0 ∂P)
    (hIntW : ∀ s : ℝ, 0 < s → Integrable
      (fun ω => if active s ω then w (z s ω) else 0) P)
    (hIntGen : ∀ s : ℝ, 0 < s → Integrable
      (fun ω => if active s ω then X.generator w (z s ω) else 0) P)
    (hHJB : ∀ s : ℝ, 0 < s → ∀ ω, active s ω = true →
      X.generator w (z s ω) ≤ q * w (z s ω))
    (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-(q * t)) * f t ≤ f 0 := by sorry
