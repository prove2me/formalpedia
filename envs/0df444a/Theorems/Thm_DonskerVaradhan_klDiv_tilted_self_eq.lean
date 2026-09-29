-- Prove2me | Theorems.Thm_DonskerVaradhan_klDiv_tilted_self_eq
-- name    : DonskerVaradhan.klDiv_tilted_self_eq
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-23T02:50:26.817149+00:00
-- url     : https://prove2.me/theorems/8fb1a3ce-bd87-4a95-82e7-601a2e4fd230
-- title:
--   Gibbs variational identity at the optimiser
-- statement:
--   **Donsker–Varadhan / Gibbs variational identity (value at the optimizer).** Let $\mu$ be a probability measure on $\alpha$ and $f:\alpha\to\mathbb{R}$ a function with $e^{f}$ integrable with respect to $\mu$, and assume $f$ is integrable against the tilted (Gibbs) measure $\mu_f := \mu.\mathrm{tilted}\,f$ whose density with respect to $\mu$ is $e^{f}/\int e^{f}\,d\mu$. Then the Kullback–Leibler divergence of the tilt satisfies $$\mathrm{KL}(\mu_f \,\|\, \mu) = \int f\,d\mu_f - \log\!\int e^{f}\,d\mu.$$ This is the value attained by the Donsker–Varadhan supremum $\sup_{Q}\big(\int f\,dQ - \mathrm{KL}(Q\|\mu)\big)$ at the optimizer $Q=\mu_f$, namely $\log\int e^{f}\,d\mu$ once rearranged. Boucheron–Lugosi–Massart, *Concentration Inequalities* (OUP 2013), Theorem 4.13 / Corollary 4.14.

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Tilted
open Real MeasureTheory Set
open scoped ENNReal NNReal

theorem DonskerVaradhan.klDiv_tilted_self_eq {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {f : α → ℝ} [IsProbabilityMeasure μ] (hf : Integrable (fun x => exp (f x)) μ) (hf_int : Integrable f (μ.tilted f)) : (InformationTheory.klDiv (μ.tilted f) μ).toReal = ∫ x, f x ∂(μ.tilted f) - log (∫ x, exp (f x) ∂μ) := by sorry
