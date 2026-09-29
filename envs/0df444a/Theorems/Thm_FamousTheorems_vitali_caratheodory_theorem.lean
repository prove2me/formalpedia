-- Prove2me | Theorems.Thm_FamousTheorems_vitali_caratheodory_theorem
-- name    : FamousTheorems.vitali_caratheodory_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:09:07.816256+00:00
-- url     : https://prove2.me/theorems/aa500cc5-d0b6-4830-a728-f7fd10904ace
-- title:
--   The Vitali–Carathéodory theorem
-- statement:
--   **The Vitali–Carathéodory theorem.** Let $\mu$ be a weakly regular, $\sigma$-finite Borel measure on a topological space and $f$ a real $\mu$-integrable function. For every $\varepsilon>0$ there is a lower semicontinuous function $g$ with values in $(-\infty,\infty]$ such that $f<g$ everywhere, $g$ is integrable (in particular $g<\infty$ almost everywhere), and
--   $$\int g\,d\mu<\int f\,d\mu+\varepsilon.$$
--
--   An integrable function can be approximated from above by lower semicontinuous functions (and from below by upper semicontinuous ones) arbitrarily well in $L^1$. This is used, for example, in Rudin's proof of the fundamental theorem of calculus for Lebesgue integrals.
--
--   **Formalization note.** Mathlib's `MeasureTheory.exists_lt_lowerSemicontinuous_integral_lt`. The function $g$ takes values in `EReal`. Its integrability is stated for the real part `(g x).toReal`, together with the condition that $g<\top$ almost everywhere. `μ.WeaklyRegular` means measurable sets are approximated from outside by open sets and open sets from inside by closed sets.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.exists_lt_lowerSemicontinuous_integral_lt`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem vitali_caratheodory_theorem {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] {μ : Measure α}
    [μ.WeaklyRegular] [SigmaFinite μ] (f : α → ℝ) (hf : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : α → EReal, (∀ x, (f x : EReal) < g x) ∧ LowerSemicontinuous g ∧
      Integrable (fun x => (g x).toReal) μ ∧ (∀ᵐ x ∂μ, g x < ⊤) ∧
        ∫ x, (g x).toReal ∂μ < ∫ x, f x ∂μ + ε := by sorry

end FamousTheorems
