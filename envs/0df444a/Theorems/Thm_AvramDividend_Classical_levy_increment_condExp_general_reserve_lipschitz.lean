-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_general_reserve_lipschitz
-- name    : AvramDividend.Classical.levy_increment_condExp_general_reserve_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T18:10:49.97541+00:00
-- url     : https://prove2.me/theorems/6a0881ef-ae88-4638-9bff-45e826da51a8
-- title:
--   General conditional Lévy Markov identity from adapted Lipschitz reserve approximations
-- statement:
--   For a spectrally negative Lévy process, a Lipschitz payoff and finite-valued adapted reserve approximations with vanishing scaled ordinary L1 error, assume deterministic increment payoff integrability, the integrability of the shifted actual payoffs and measurability/integrability of the respective conditional and transition differences. Then the conditional expectation at the general reserve equals the Lévy transition expectation almost everywhere. Combine the separately Proved conditional-expectation and transition-operator L1 stability lemmas to establish both convergence conditions, then apply the independently Proved general-reserve L1 limit transfer lemma. The adapted approximants and stopped HJB verification remain independent obligations.
-- source:
--   Accepted levy's conditional L1 stability candidate 12825, transition random-reserve L1 continuity candidate 12881, and published general-reserve simple L1 Markov theorem currently coordinator-owned.

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_condExp_lipschitz_L1_approximation_stability
import Theorems.Thm_AvramDividend_Classical_levy_transition_random_reserve_L1_continuity
import Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_general_reserve_of_simple_L1

open Filter MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_increment_condExp_general_reserve_lipschitz
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (f : ℝ → ℝ) (hf : Measurable f) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (hInt : ∀ x : ℝ, Integrable
      (fun η => f (x + X.X (t - s) η)) P)
    (Sn : ℕ → SimpleFunc Ω ℝ) (Z : Ω → ℝ)
    (hSn : ∀ n, Measurable[𝓕 s] (Sn n : Ω → ℝ))
    (hZ : Integrable (fun ω =>
      f (Z ω + (X.X t ω - X.X s ω))) P)
    (hZn : ∀ n, Integrable (fun ω =>
      f (Sn n ω + (X.X t ω - X.X s ω))) P)
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
    (hDom : ∀ n, Integrable
      (fun ω => L * |Sn n ω - Z ω|) P)
    (hlim : Tendsto (fun n : ℕ =>
      ∫ ω, L * |Sn n ω - Z ω| ∂P)
      atTop (nhds 0)) :
    P[(fun η => f (Z η + (X.X t η - X.X s η))) | 𝓕 s] =ᵐ[P]
      (fun ω => ∫ η, f (Z ω + X.X (t - s) η) ∂P) := by sorry
