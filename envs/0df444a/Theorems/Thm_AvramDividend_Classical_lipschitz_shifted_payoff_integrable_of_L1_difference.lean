-- Prove2me | Theorems.Thm_AvramDividend_Classical_lipschitz_shifted_payoff_integrable_of_L1_difference
-- name    : AvramDividend.Classical.lipschitz_shifted_payoff_integrable_of_L1_difference
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T18:35:57.984114+00:00
-- url     : https://prove2.me/theorems/cab2b0d5-e7b6-4ca2-a493-741be37c405c
-- title:
--   Integrability stability of Lipschitz shifted payoffs under an integrable state difference
-- statement:
--   Let f be a measurable Lipschitz real payoff, let Zn, Z and Y be measurable real random variables, assume the shifted payoff f(Z+Y) is integrable, and assume the scaled absolute state error L|Zn-Z| is integrable. Then the shifted payoff f(Zn+Y) is integrable. The Lipschitz bound gives pointwise domination of the payoff difference by the integrable state error. Strong measurability follows from composition with measurable random variables. Use Mathlib Integrable.mono and addition of integrable functions to transfer integrability. This proves an analytic side condition for canonical random-reserve approximations without requiring a global moment bound on all payoffs.
-- source:
--   Exact Mathlib Integrable.mono indexed at the pinned revision; uses only Mathlib and no pending Prove2Me imports. Remote compiler remains authoritative.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Tactic.Ring

open MeasureTheory

theorem AvramDividend.Classical.lipschitz_shifted_payoff_integrable_of_L1_difference
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (f : ℝ → ℝ) (hf : Measurable f) (L : ℝ)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (Zn Z Y : Ω → ℝ)
    (hZn : Measurable Zn) (hZ : Measurable Z)
    (hY : Measurable Y)
    (hBase : Integrable (fun ω => f (Z ω + Y ω)) P)
    (hDom : Integrable (fun ω => L * |Zn ω - Z ω|) P) :
    Integrable (fun ω => f (Zn ω + Y ω)) P := by sorry
