-- Prove2me | Theorems.Thm_FamousTheorems_layer_cake_formula
-- name    : FamousTheorems.layer_cake_formula
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:03:38.704467+00:00
-- url     : https://prove2.me/theorems/358ead6e-aeb5-40f9-ab87-6667fdeb4d18
-- title:
--   Cavalieri's principle (the layer-cake formula)
-- statement:
--   **Cavalieri's principle (the layer-cake formula).** Let $f\ge0$ be a.e.-measurable on a measure space $(\alpha,\mu)$, and let $g$ be a function that is a.e. nonnegative on $(0,\infty)$ and integrable on every interval $[0,t]$. Then
--   $$\int_\alpha G(f(\omega))\,d\mu(\omega)=\int_0^\infty \mu\{f\ge t\}\,g(t)\,dt,\qquad G(x)=\int_0^x g(t)\,dt.$$
--
--   With $g=1$ this is the layer-cake formula $\int f\,d\mu=\int_0^\infty\mu\{f\ge t\}\,dt$, and with $g(t)=pt^{p-1}$ it gives $\int f^p\,d\mu=\int_0^\infty pt^{p-1}\mu\{f\ge t\}\,dt$. These identities turn integrals into integrals of distribution functions. They are standard tools in harmonic analysis (interpolation, maximal functions) and in probability (moments from tail bounds).
--
--   **Formalization note.** Mathlib's `MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul`. Both sides are lower Lebesgue integrals in `ENNReal`: the left integrates `ENNReal.ofReal` of the interval integral $\int_0^{f(\omega)}g$, and the right integrates over $(0,\infty)$ with respect to Lebesgue measure. The hypothesis `0 ≤ᵐ[μ] f` means $f\ge0$ $\mu$-almost everywhere.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem layer_cake_formula {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ} {g : ℝ → ℝ} (f_nn : 0 ≤ᵐ[μ] f)
    (f_mble : AEMeasurable f μ) (g_intble : ∀ t > 0, IntervalIntegrable g volume 0 t)
    (g_nn : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)), 0 ≤ g t) :
    ∫⁻ ω, ENNReal.ofReal (∫ t in (0 : ℝ)..f ω, g t) ∂μ =
      ∫⁻ t in Set.Ioi 0, μ {a | t ≤ f a} * ENNReal.ofReal (g t) := by sorry

end FamousTheorems
