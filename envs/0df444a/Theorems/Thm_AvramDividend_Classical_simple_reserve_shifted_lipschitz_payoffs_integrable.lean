-- Prove2me | Theorems.Thm_AvramDividend_Classical_simple_reserve_shifted_lipschitz_payoffs_integrable
-- name    : AvramDividend.Classical.simple_reserve_shifted_lipschitz_payoffs_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T20:35:44.107981+00:00
-- url     : https://prove2.me/theorems/ada3b63e-6a89-45cd-988b-b32bbb9b8d23
-- title:
--   Integrability of all canonical simple-reserve shifted payoffs under a Lipschitz envelope
-- statement:
--   For a measurable integrable real reserve Z, a measurable real shift Y and a measurable Lipschitz payoff f, assume that f(Z+Y) is integrable. The canonical finite-valued SimpleFunc.approxOn approximations of Z have integrable shifted payoffs f(S_n+Y) for every n. Their differences from Z are integrable and Lipschitz domination transfers payoff integrability through the separately Proved integrable-difference theorem. This removes a whole sequence of shifted-payoff integrability premises in subsequent conditional Lévy Markov proofs.
-- source:
--   Chat 08 accepted lipschitz shifted integrable lemma target cab2b0d5-e7b6-4ca2-a493-741be37c405c; uses Mathlib SimpleFunc.integrable_approxOn_range.

import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_lipschitz_shifted_payoff_integrable_of_L1_difference

open MeasureTheory Set
open AvramDividend.Classical

theorem AvramDividend.Classical.simple_reserve_shifted_lipschitz_payoffs_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (f : ℝ → ℝ) (hf : Measurable f)
    (L : ℝ)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (Z Y : Ω → ℝ)
    (hZ : Measurable Z) (hY : Measurable Y)
    (hZI : Integrable Z P)
    (hBase : Integrable (fun ω => f (Z ω + Y ω)) P) :
    ∀ n : ℕ, Integrable (fun ω =>
      f ((SimpleFunc.approxOn Z hZ (Set.range Z ∪ {0}) 0
        (by simp) n) ω + Y ω)) P := by sorry
