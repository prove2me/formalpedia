-- Prove2me | Theorems.Thm_FamousTheorems_lebesgue_differentiation
-- name    : FamousTheorems.lebesgue_differentiation
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T09:15:24.943627+00:00
-- url     : https://prove2.me/theorems/93b04194-593b-47fa-9b45-05ce292ee2f9
-- title:
--   The Lebesgue differentiation theorem
-- statement:
--   **The Lebesgue differentiation theorem (Vitali family form).** Let $\mu$ be a locally finite measure on a second-countable metric space with a Vitali family $v$, and $f\ge0$ a.e.-measurable with $\int f\,d\mu<\infty$. Then for $\mu$-almost every $x$,
--   $$\frac{1}{\mu(a)}\int_a f\,d\mu\longrightarrow f(x)\qquad\text{as } a \text{ shrinks to } x \text{ along } v .$$
--
--   For Lebesgue measure and balls this says the average of an integrable function over small balls converges to its value almost everywhere. It is the measure-theoretic form of the fundamental theorem of calculus and the starting point of differentiation of measures.
--
--   **Formalization note.** Mathlib's `VitaliFamily.ae_tendsto_lintegral_div` (lower Lebesgue integral, `ℝ≥0∞`-valued). `v.filterAt x` is the filter of sets of the Vitali family shrinking to `x`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `VitaliFamily.ae_tendsto_lintegral_div`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem lebesgue_differentiation {α : Type*} [PseudoMetricSpace α] {m0 : MeasurableSpace α} {μ : Measure α} (v : VitaliFamily μ)
    [SecondCountableTopology α] [BorelSpace α] [IsLocallyFiniteMeasure μ] {f : α → ENNReal}
    (hf : AEMeasurable f μ) (h'f : ∫⁻ y, f y ∂μ ≠ ⊤) :
    ∀ᵐ x ∂μ, Filter.Tendsto (fun a => (∫⁻ y in a, f y ∂μ) / μ a) (v.filterAt x) (nhds (f x)) := by sorry

end FamousTheorems
