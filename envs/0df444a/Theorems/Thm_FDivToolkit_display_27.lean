-- Prove2me | Theorems.Thm_FDivToolkit_display_27
-- name    : FDivToolkit.display_27
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:23:12.627733+00:00
-- url     : https://prove2.me/theorems/37f63aa9-0262-4d70-bdb2-c64a290ad6ab
-- title:
--   Display (27), proof of Proposition 1, p.31 — $K$ is finite under (5)
-- statement:
--   Let $H$ be a generating function and $\nu$ a reference model with density $f$ satisfying (5). Then for all $(\alpha_1,\alpha_2)\in\mathbb R^2$,
--   $$
--   K(\alpha_1,\alpha_2)=\int_{\mathcal S}F^*(\alpha_1+\alpha_2x)f(x)\,dx<\infty.
--   $$
--
--   This is the hypothesis under which the results of Breuer and Csiszár apply.
--
--   Differences from the source:
--   - reading: K : ℝ² → (−∞, ∞], and K(α₁, α₂) < ∞ → the integrand of K is Bochner integrable; reason: the integrand is bounded below by the f-integrable function α₁ + α₂x, so K < ∞ is integrability
--   - encoding: distributions ν, η on 𝓢 with densities f, g → functions f, g : ℝ → ℝ with IsRefModel f and IsDensity g, the distributions being densityMeasure f and densityMeasure g, and integrals over 𝓢 written over ℝ where f or g vanishes off 𝓢; reason: the paper uses its distributions only through their densities; measurability is the standing convention of the field, and f = 0 off 𝓢 by footnote 2
-- source:
--   Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), display (27) and following text, proof of Proposition 1, p.31

import Definitions.Def_FDivToolkit_IsRefModel
import Definitions.Def_FDivToolkit_Cond5
import Definitions.Def_FDivToolkit_Fstar

open MeasureTheory

namespace FDivToolkit

/-- Finiteness of `K`, the conclusion of the chain of inequalities (27), Kruse, Schneider & Schweizer,
SSRN 3680475 (Aug 25, 2020), proof of Proposition 1, p.31: under (5), `K(α₁, α₂) < ∞` for all
`(α₁, α₂) ∈ ℝ²`.

**Formalization Note.** `K` takes values in `(−∞, ∞]` on p.31: its integrand is bounded below by the
`f`-integrable function `α₁ + α₂x`. So `K < ∞` is integrability of the integrand. -/
theorem display_27 {H f : ℝ → ℝ} (hH : IsAdmissibleH H) (hf : IsRefModel f) (h5 : Cond5 H f)
    (α : ℝ × ℝ) : Integrable fun x => Fstar H (α.1 + α.2 * x) * f x := by sorry

end FDivToolkit
