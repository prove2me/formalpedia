-- Prove2me | solution 1 for thm_8_5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:17:47.565459+00:00
-- url     : https://prove2.me/submissions/dd977af5-06a4-42db-a257-fb06eab0005e

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic


/-

  # Theorem 8.5 Fubini theorem

-/

/-
\begin{thmbox}{8.5 (Fubini Theorem)}
Let $f$ be a real-valued or complex-valued measurable function defined on the product space $(\mathcal{X}\times \mathcal{Y},\mathcal{F}\times \mathcal{G})$. Let $P$ and $Q$ be $\sigma$-finite measures defined on $\mathcal{X}$ and $\mathcal{Y}$, respectively. If one of the following integrals is finite:
\[
\int_{\mathcal{X}} \int_{\mathcal{Y}} |f(x,y)|\, dQ(y)\, dP(x), \qquad
\int_{\mathcal{Y}} \int_{\mathcal{X}} |f(x,y)|\, dP(x)\, dQ(y),
\]
\[
\int_{\mathcal{X}\times \mathcal{Y}} |f(x,y)|\, d(P\times Q),
\]
then $f\in L^1(P\times Q)$ and
\[
\int_{\mathcal{X}} \int_{\mathcal{Y}} f(x,y)\, dQ(y)\, dP(x)
=
\int_{\mathcal{Y}} \int_{\mathcal{X}} f(x,y)\, dP(x)\, dQ(y)
\]
\[
=
\int_{\mathcal{X}\times \mathcal{Y}} f(x,y)\, d(P\times Q).
\]
\end{thmbox}
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal


theorem solution
    {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β)
    [SigmaFinite P] [SigmaFinite Q]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : α × β → E}
    (hf_meas : AEStronglyMeasurable f (P.prod Q))
    (hfinite :
      ((∫⁻ x, ∫⁻ y, ‖f (x, y)‖ₑ ∂Q ∂P) < ∞) ∨
      ((∫⁻ y, ∫⁻ x, ‖f (x, y)‖ₑ ∂P ∂Q) < ∞) ∨
      ((∫⁻ z, ‖f z‖ₑ ∂(P.prod Q)) < ∞)) :
    Integrable f (P.prod Q) ∧
      Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂Q) P ∧
      Integrable (fun y => ∫ x, ‖f (x, y)‖ ∂P) Q ∧
      (∫ x, ∫ y, f (x, y) ∂Q ∂P = ∫ y, ∫ x, f (x, y) ∂P ∂Q) ∧
      (∫ x, ∫ y, f (x, y) ∂Q ∂P = ∫ z, f z ∂(P.prod Q)) := by
  have hnorm_aemeas :
      AEMeasurable (fun z : α × β => ‖f z‖ₑ) (P.prod Q) :=
    hf_meas.enorm
  have hprod_lintegral :
      (∫⁻ z, ‖f z‖ₑ ∂(P.prod Q)) < ∞ := by
    rcases hfinite with hleft | hrest
    · rwa [MeasureTheory.lintegral_prod (fun z : α × β => ‖f z‖ₑ) hnorm_aemeas]
    · rcases hrest with hright | hprod
      · rwa [MeasureTheory.lintegral_prod_symm (fun z : α × β => ‖f z‖ₑ) hnorm_aemeas]
      · exact hprod
  have hf : Integrable f (P.prod Q) :=
    ⟨hf_meas, hprod_lintegral⟩
  have hswap :
      (∫ x, ∫ y, f (x, y) ∂Q ∂P) = ∫ y, ∫ x, f (x, y) ∂P ∂Q := by
    simpa using
      (integral_integral_swap (μ := P) (ν := Q) (f := fun x y => f (x, y)) hf)
  have hprod :
      (∫ z, f z ∂(P.prod Q)) = ∫ x, ∫ y, f (x, y) ∂Q ∂P := by
    simpa using (integral_prod (μ := P) (ν := Q) f hf)
  exact ⟨hf, hf.integral_norm_prod_left, hf.integral_norm_prod_right, hswap, hprod.symm⟩