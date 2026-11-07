-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_discounted_stopped_C2_jet_uniform_bound
-- name    : AvramDividend.Classical.avram_wave7_18_original_discounted_stopped_C2_jet_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:28:00.636444+00:00
-- url     : https://prove2.me/theorems/2cca9323-b3bb-4c27-8ec4-34eba32c33bf
-- title:
--   Discounted original stopped C² reserve jet has uniform deterministic pre-exit bound
-- statement:
--   For the original spectrally negative Lévy controlled post-payment reserve and a positive discount q, the exponential discount exp(-qs) lies in (0,1] at every nonnegative time. Combining this with the Proved original dense-clock pre-exit uniform C² jet bound yields one deterministic bound for the discounted value, first derivative and second derivative at all strict times before the original right-continuous-filtration stopped exit. The source cap condition is unchanged and includes C=∞. This is a pathwise finite-horizon integrand estimate; compensation, Itô and stochastic square integrability are owned by separate lemmas.

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_stopped_preexit_C2_jet_uniform_deterministic_bound

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_18_original_discounted_stopped_C2_jet_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 < q)
    (r : ℕ → ℝ≥0) (lower upper : ℝ)
    (hlower : 0 < lower) (hlu : lower ≤ upper)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (hdense : DenseRange r) (B : ℝ≥0) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (ω : Ω) (T : ℝ≥0),
        (T : WithTop ℝ≥0) ≤
          min (⨅ k : ℕ,
            if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
                upper < x + X.X (r k) ω - rightLimit D (r k) ω
            then (r k : WithTop ℝ≥0) else ⊤) (B : WithTop ℝ≥0) →
        ∀ (s : ℝ≥0), s < T →
          |Real.exp (-(q * (s : ℝ))) *
             w (x + X.X s ω - rightLimit D s ω)| ≤ M ∧
          |Real.exp (-(q * (s : ℝ))) *
             deriv w (x + X.X s ω - rightLimit D s ω)| ≤ M ∧
          |Real.exp (-(q * (s : ℝ))) *
             deriv (deriv w) (x + X.X s ω - rightLimit D s ω)| ≤ M := by sorry
