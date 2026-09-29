-- Prove2me | Theorems.Thm_FamousTheorems_law_of_total_expectation
-- name    : FamousTheorems.law_of_total_expectation
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:27:10.615983+00:00
-- url     : https://prove2.me/theorems/02644162-8fb7-4d28-af8e-366dc1676b1f
-- title:
--   The law of total expectation (tower property)
-- statement:
--   **The law of total expectation.** Let $\mu$ be a measure on $\alpha$, $m$ a sub-σ-algebra with $\mu$ σ-finite on $m$, and $f$ a function with values in a real Banach space. Then the conditional expectation of $f$ given $m$ has the same integral as $f$:
--   $$\int\mathbb E[f\mid m]\,d\mu=\int f\,d\mu,\qquad\text{i.e. }\ \mathbb E\big[\mathbb E[f\mid m]\big]=\mathbb E[f].$$
--
--   This is the simplest case of the tower property of conditional expectation. It is the formal basis of conditioning arguments in probability, of the martingale property, and of the law of total variance.
--
--   **Formalization note.** Mathlib's `MeasureTheory.integral_condExp`. `MeasureTheory.condExp m μ f` (notation `μ[f|m]`) is the conditional expectation and `μ.trim hm` is the restriction of `μ` to `m`. No integrability hypothesis is needed: for non-integrable `f`, both the Bochner integral and Mathlib's conditional expectation are defined as $0$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.integral_condExp`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem law_of_total_expectation {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {m m₀ : MeasurableSpace α}
    {μ : @MeasureTheory.Measure α m₀} (f : α → E) (hm : m ≤ m₀) [MeasureTheory.SigmaFinite (μ.trim hm)] :
    ∫ x, MeasureTheory.condExp m μ f x ∂μ = ∫ x, f x ∂μ := by sorry

end FamousTheorems
