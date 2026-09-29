-- Prove2me | Theorems.Thm_BanditAlgorithm_integrable_exp_neg_quadratic_add_linear
-- name    : BanditAlgorithm.integrable_exp_neg_quadratic_add_linear
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T21:28:01.91143+00:00
-- url     : https://prove2.me/theorems/316630e0-ce24-4102-be17-45504015a8a1
-- title:
--   A Gaussian with a linear term is integrable
-- statement:
--   For $a>0$ and any $c\in\mathbb R$ the function $x\mapsto e^{-ax^2+cx}$ is Lebesgue integrable on $\mathbb R$.
--
--   Mathlib has integrability of the pure Gaussian $e^{-ax^2}$ but not of the completed-square form with a linear term. The two are related by the translation $x\mapsto x-\tfrac{c}{2a}$, which is also what evaluates the integral, so this lemma is the integrability half of the Gaussian-with-linear-term package and is what lets the method-of-mixtures computation be transported from Bochner integrals to $[0,\infty]$-valued ones, where Tonelli's theorem applies.
-- source:
--   Standard: the integrability companion to the completed-square Gaussian integral. Needed to transport the mixture computation from Bochner integrals to [0, infinity]-valued ones.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open MeasureTheory Real

theorem BanditAlgorithm.integrable_exp_neg_quadratic_add_linear {a : ℝ} (ha : 0 < a)
    (c : ℝ) :
    MeasureTheory.Integrable (fun x : ℝ ↦ Real.exp (-a * x ^ 2 + c * x)) := by
  sorry
