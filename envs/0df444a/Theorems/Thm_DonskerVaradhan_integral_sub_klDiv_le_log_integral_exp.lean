-- Prove2me | Theorems.Thm_DonskerVaradhan_integral_sub_klDiv_le_log_integral_exp
-- name    : DonskerVaradhan.integral_sub_klDiv_le_log_integral_exp
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-23T02:50:33.32007+00:00
-- url     : https://prove2.me/theorems/69e0e272-612c-4c24-98dd-8c8b83e4aef1
-- title:
--   Donsker–Varadhan variational inequality
-- statement:
--   **Donsker–Varadhan variational inequality.** For probability measures $Q \ll \mu$ on $\alpha$ with integrable log-likelihood ratio, and $f:\alpha\to\mathbb{R}$ with $e^{f}$ integrable against $\mu$ and $f$ integrable against $Q$, one has $$\int f\,dQ - \mathrm{KL}(Q\,\|\,\mu) \le \log\!\int e^{f}\,d\mu.$$ Together with the equality at the tilt $Q=\mu.\mathrm{tilted}\,f$, this is the full Donsker–Varadhan formula $\log\int e^{f}\,d\mu = \sup_{Q\ll\mu}\big(\int f\,dQ - \mathrm{KL}(Q\|\mu)\big)$. The proof is Gibbs' inequality $\mathrm{KL}(Q\,\|\,\mu.\mathrm{tilted}\,f)\ge 0$ expanded through the tilted log-likelihood ratio. Boucheron–Lugosi–Massart, *Concentration Inequalities* (OUP 2013), Theorem 4.13 / Corollary 4.14.

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Tilted
open Real MeasureTheory Set
open scoped ENNReal NNReal

theorem DonskerVaradhan.integral_sub_klDiv_le_log_integral_exp {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {f : α → ℝ} {Q : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q] (hQμ : Q ≪ μ) (hf : Integrable (fun x => exp (f x)) μ) (hf_int : Integrable f Q) (h_llr : Integrable (llr Q μ) Q) : ∫ x, f x ∂Q - (InformationTheory.klDiv Q μ).toReal ≤ log (∫ x, exp (f x) ∂μ) := by sorry
