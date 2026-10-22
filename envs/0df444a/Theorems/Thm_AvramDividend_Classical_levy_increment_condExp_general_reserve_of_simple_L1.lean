-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_general_reserve_of_simple_L1
-- name    : AvramDividend.Classical.levy_increment_condExp_general_reserve_of_simple_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T17:59:33.635808+00:00
-- url     : https://prove2.me/theorems/f8d739d5-67c1-4c00-ad7e-fee1d6c9922e
-- title:
--   General random-reserve conditional Lévy Markov identity from adapted simple-state L1 approximations
-- statement:
--   Fix a spectrally negative Lévy process, s≤t, a measurable payoff f with integrable deterministic stationary-increment payoffs, a general random starting reserve Z and a sequence of finite-valued Mathlib simple-function reserves S_n that are measurable in F_s. Assume the conditional expected shifted payoffs at S_n and at Z, and the deterministic Lévy transition payoffs at S_n and at Z, are strongly measurable and integrable in the specified L1 differences. Assume both sequences of absolute L1 differences converge to zero. Then the conditional expectation of f(Z+X_t−X_s) given F_s agrees almost everywhere with the deterministic transition expectation starting from Z. For each n use the already Proved simple-reserve finite-valued Markov identity to equate the two approximations almost everywhere, then invoke the separately Proved real_L1_common_ae_limit theorem to pass that equality to the limits. This theorem establishes the formal L1 limiting step under explicit analytic hypotheses. Discharging those hypotheses from the integrable adapted reserve and canonical simple-function approximants is a separate obligation. Do not interpret this as proving stopped HJB verification.
-- source:
--   Proved levy_increment_condExp_simple_reserve target 2ed4ca22-e5f1-46c5-b161-6e9d862a0bc8 and dependency-gated real_L1_common_ae_limit target 41061f11-53b5-4296-aeb1-fdd90670c737 (candidate 12882 pending when drafted).

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_simple_reserve
import Theorems.Thm_AvramDividend_Classical_real_L1_common_ae_limit

open Filter MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_increment_condExp_general_reserve_of_simple_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (f : ℝ → ℝ) (hf : Measurable f)
    (hInt : ∀ x : ℝ, Integrable
      (fun η => f (x + X.X (t - s) η)) P)
    (Sn : ℕ → SimpleFunc Ω ℝ) (Z : Ω → ℝ)
    (hSn : ∀ n, Measurable[𝓕 s] (Sn n : Ω → ℝ))
    (hCStrong : ∀ n, StronglyMeasurable
      (P[(fun η => f (Sn n η + (X.X t η - X.X s η))) | 𝓕 s]))
    (hTStrong : ∀ n, StronglyMeasurable
      (fun ω => ∫ η, f (Sn n ω + X.X (t - s) η) ∂P))
    (hC0Strong : StronglyMeasurable
      (P[(fun η => f (Z η + (X.X t η - X.X s η))) | 𝓕 s]))
    (hT0Strong : StronglyMeasurable
      (fun ω => ∫ η, f (Z ω + X.X (t - s) η) ∂P))
    (hCDiff : ∀ n, Integrable (fun ω =>
      (P[(fun η => f (Sn n η + (X.X t η - X.X s η))) | 𝓕 s]) ω -
      (P[(fun η => f (Z η + (X.X t η - X.X s η))) | 𝓕 s]) ω) P)
    (hTDiff : ∀ n, Integrable (fun ω =>
      (∫ η, f (Sn n ω + X.X (t - s) η) ∂P) -
      (∫ η, f (Z ω + X.X (t - s) η) ∂P)) P)
    (hCLim : Tendsto (fun n : ℕ =>
      ∫ ω, |(P[(fun η =>
          f (Sn n η + (X.X t η - X.X s η))) | 𝓕 s]) ω -
        (P[(fun η =>
          f (Z η + (X.X t η - X.X s η))) | 𝓕 s]) ω| ∂P)
      atTop (nhds 0))
    (hTLim : Tendsto (fun n : ℕ =>
      ∫ ω, |(∫ η, f (Sn n ω + X.X (t - s) η) ∂P) -
        (∫ η, f (Z ω + X.X (t - s) η) ∂P)| ∂P)
      atTop (nhds 0)) :
    P[(fun η => f (Z η + (X.X t η - X.X s η))) | 𝓕 s] =ᵐ[P]
      (fun ω => ∫ η, f (Z ω + X.X (t - s) η) ∂P) := by sorry
