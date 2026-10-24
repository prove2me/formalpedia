-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_upper_grid_discount_integrable
-- name    : AvramDividend.Classical.levy_upper_grid_discount_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:22:01.911506+00:00
-- url     : https://prove2.me/theorems/933b920e-3aed-4833-aa14-835a04fbfb01
-- title:
--   Integrability of the stopped discount at a capped upper-only Lévy grid crossing
-- statement:
--   Under the exact deterministic upper-only sampled first passage index K=hittingBtwn X(clock k) (Ioi z) 0 m and nonnegative q, the real-valued payoff indicator 1_{z<X(clock K)} exp(-q*clock K) is integrable with respect to the Lévy probability measure P. The accepted upper-only stopped reserve/time measurability lemma gives measurability of both reserve and sampled time; since q and clock K are nonnegative, the payoff is bounded by one, so Integrable.of_bound applies.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_upper_grid_stopped_reserve_time_measurable
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_upper_grid_discount_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕 (clock k))
    (z : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => X.X (clock k) ω) (Ioi z) 0 m ω)
    (q : ℝ) (hq : 0 ≤ q) :
    Integrable ({ω : Ω | z < X.X (clock (K ω)) ω}.indicator
      (fun ω => Real.exp (-((clock (K ω)) : ℝ) * q))) P := by sorry
