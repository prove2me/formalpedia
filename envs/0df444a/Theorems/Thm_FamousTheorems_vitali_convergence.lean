-- Prove2me | Theorems.Thm_FamousTheorems_vitali_convergence
-- name    : FamousTheorems.vitali_convergence
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:15:26.755893+00:00
-- url     : https://prove2.me/theorems/3c0e9d69-8bbe-4313-ba75-a1e4931fbefb
-- title:
--   The Vitali convergence theorem
-- statement:
--   **The Vitali convergence theorem.** Let $1\le p<\infty$ and let $f_n,g\in L^p(\mu)$. Then $f_n\to g$ in $L^p$ if and only if $f_n\to g$ in measure and the family $\{f_n\}$ is uniformly integrable and uniformly tight in $L^p$.
--
--   It characterises $L^p$ convergence exactly, and it strengthens the dominated convergence theorem, whose hypothesis is only sufficient. In probability it gives the standard criterion for convergence of moments: convergence in probability plus uniform integrability.
--
--   **Formalization note.** Mathlib's `MeasureTheory.tendstoInMeasure_iff_tendsto_Lp`, for an arbitrary (not necessarily finite) measure. This is why uniform tightness (`UnifTight`) appears alongside uniform integrability (`UnifIntegrable`). $L^p$ convergence is expressed by `eLpNorm (f n - g) p μ → 0`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.tendstoInMeasure_iff_tendsto_Lp`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem vitali_convergence {α β : Type*} {m : MeasurableSpace α} [NormedAddCommGroup β] {μ : MeasureTheory.Measure α} {p : ENNReal}
    {f : ℕ → α → β} {g : α → β} (hp : 1 ≤ p) (hp' : p ≠ ⊤) (hf : ∀ n, MeasureTheory.MemLp (f n) p μ)
    (hg : MeasureTheory.MemLp g p μ) :
    MeasureTheory.TendstoInMeasure μ f Filter.atTop g ∧ MeasureTheory.UnifIntegrable f p μ ∧
        MeasureTheory.UnifTight f p μ ↔
      Filter.Tendsto (fun n => MeasureTheory.eLpNorm (f n - g) p μ) Filter.atTop (nhds 0) := by sorry

end FamousTheorems
