-- Prove2me | Theorems.Thm_FamousTheorems_law_of_unconscious_statistician
-- name    : FamousTheorems.law_of_unconscious_statistician
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:09:49.887006+00:00
-- url     : https://prove2.me/theorems/22dba151-0a6b-4c85-9677-32e824dc22cd
-- title:
--   The law of the unconscious statistician
-- statement:
--   **The law of the unconscious statistician.** Let $X$ be a random variable on a finite measure space $(\Omega,\mathbb P)$ with a density $p_X$ with respect to a measure $\mu$ on $E$, and let $f:E\to F$ be $\mu$-a.e. strongly measurable. Then
--   $$\int_E p_X(x)\,f(x)\,d\mu(x)=\int_\Omega f(X(\omega))\,d\mathbb P(\omega).$$
--
--   The expectation of $f(X)$ can be computed from the distribution of $X$ without finding the distribution of $f(X)$. This is how expectations are computed in practice, for example $\mathbb E[X^2]=\int x^2p(x)\,dx$.
--
--   **Formalization note.** Mathlib's `MeasureTheory.pdf.integral_pdf_smul`. `HasPDF X P μ` says that the law of $X$ under $P$ has a density with respect to $\mu$, and `pdf X P μ` is that density, with values in $[0,\infty]$ (converted with `toReal`). $f$ takes values in a real normed space and both sides are Bochner integrals.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.pdf.integral_pdf_smul`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem law_of_unconscious_statistician {Ω E F : Type*} [MeasurableSpace E] {m : MeasurableSpace Ω} {P : Measure Ω} {μ : Measure E}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [IsFiniteMeasure P] {X : Ω → E} [HasPDF X P μ] {f : E → F}
    (hf : AEStronglyMeasurable f μ) :
    ∫ x, (pdf X P μ x).toReal • f x ∂μ = ∫ ω, f (X ω) ∂P := by sorry

end FamousTheorems
