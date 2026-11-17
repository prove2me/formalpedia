-- Prove2me | solution 1 for thm_8_3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:16:56.90506+00:00
-- url     : https://prove2.me/submissions/31f6222a-202d-42b7-9780-70ab16b87242

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic


/-

  # Theorem 8.3 Tonelli theorem

-/

/-
\begin{thmbox}{8.3 (Tonelli Theorem)}
If $f:\mathcal{X}\times \mathcal{Y}\to \bar{\mathbb{R}}$ is $(\mathcal{F}\times \mathcal{G})$-measurable and nonnegative and $P$ and $Q$ are $\sigma$-finite measures defined on $\mathcal{X}$ and $\mathcal{Y}$, respectively, then
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
    {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure α) (Q : Measure β)
    [SigmaFinite P] [SigmaFinite Q]
    {f : α × β → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ x, ∫⁻ y, f (x, y) ∂Q ∂P)
      = ∫⁻ y, ∫⁻ x, f (x, y) ∂P ∂Q ∧
    (∫⁻ x, ∫⁻ y, f (x, y) ∂Q ∂P)
      = ∫⁻ z, f z ∂(P.prod Q) := by
  have hfae : AEMeasurable f (P.prod Q) := hf.aemeasurable
  have hswap :
      (∫⁻ x, ∫⁻ y, f (x, y) ∂Q ∂P)
        = ∫⁻ y, ∫⁻ x, f (x, y) ∂P ∂Q := by
    simpa using
      (lintegral_lintegral_swap (μ := P) (ν := Q) (f := fun x y => f (x, y)) hfae)
  have hprod :
      (∫⁻ z, f z ∂(P.prod Q)) = ∫⁻ x, ∫⁻ y, f (x, y) ∂Q ∂P := by
    simpa using (lintegral_prod (μ := P) (ν := Q) f hfae)
  refine ⟨hswap, ?_⟩
  exact hprod.symm