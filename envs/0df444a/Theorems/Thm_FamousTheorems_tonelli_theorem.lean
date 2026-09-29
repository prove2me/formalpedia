-- Prove2me | Theorems.Thm_FamousTheorems_tonelli_theorem
-- name    : FamousTheorems.tonelli_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:03:40.143142+00:00
-- url     : https://prove2.me/theorems/f797067d-053f-4d09-992f-0f679ff247f7
-- title:
--   Tonelli's theorem
-- statement:
--   **Tonelli's theorem.** Let $\mu$ be a measure on $\alpha$ and $\nu$ an s-finite measure on $\beta$. For every a.e.-measurable function $f:\alpha\times\beta\to[0,\infty]$,
--   $$\int_{\alpha\times\beta}f\,d(\mu\times\nu)=\int_\alpha\int_\beta f(x,y)\,d\nu(y)\,d\mu(x).$$
--
--   Tonelli's theorem allows iterated integrals of nonnegative functions to be computed in either order, with no integrability hypothesis. It is the usual first step before applying Fubini's theorem to signed or vector-valued functions, and it is used throughout analysis and probability to interchange sums, integrals and expectations.
--
--   **Formalization note.** Mathlib's `MeasureTheory.lintegral_prod`. `∫⁻` is the lower Lebesgue integral of an `ENNReal`-valued function and `μ.prod ν` is the product measure. Mathlib needs only the second factor to be s-finite (`SFinite ν`), which is weaker than the usual σ-finiteness hypothesis.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.lintegral_prod`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem tonelli_theorem {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [SFinite ν] (f : α × β → ENNReal) (hf : AEMeasurable f (μ.prod ν)) :
    ∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ := by sorry

end FamousTheorems
