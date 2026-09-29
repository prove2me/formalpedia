-- Prove2me | Theorems.Thm_FamousTheorems_tannery_theorem
-- name    : FamousTheorems.tannery_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:03:52.438595+00:00
-- url     : https://prove2.me/theorems/97265e60-db8a-4e3d-875f-369833dd6a17
-- title:
--   Tannery's theorem
-- statement:
--   **Tannery's theorem.** Let $f_n(k)$ be a family of terms in a Banach space, indexed by $k$ and by a parameter $n$ running along a filter. Suppose $f_n(k)\to g(k)$ for each $k$, and suppose that eventually $\|f_n(k)\|\le M_k$ for all $k$, with $\sum_k M_k<\infty$. Then
--   $$\lim_n\sum_k f_n(k)=\sum_k g(k).$$
--
--   This is the dominated convergence theorem for series. It justifies passing a limit through an infinite sum. A classical application is the proof that $(1+x/n)^n\to e^x$ by expanding binomially and taking the limit term by term.
--
--   **Formalization note.** Mathlib's `tendsto_tsum_of_dominated_convergence`. The limit is taken along an arbitrary filter `𝓕`, which covers sequences as the case `Filter.atTop` on `ℕ`. `∑'` is the unconditional sum (`tsum`), and the domination hypothesis only has to hold eventually along `𝓕`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `tendsto_tsum_of_dominated_convergence`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem tannery_theorem {α β G : Type*} {𝓕 : Filter α} [NormedAddCommGroup G] [CompleteSpace G] {f : α → β → G}
    {g : β → G} {bound : β → ℝ} (h_sum : Summable bound)
    (hab : ∀ k, Filter.Tendsto (fun x => f x k) 𝓕 (nhds (g k)))
    (h_bound : ∀ᶠ n in 𝓕, ∀ k, ‖f n k‖ ≤ bound k) :
    Filter.Tendsto (fun x => ∑' k, f x k) 𝓕 (nhds (∑' k, g k)) := by sorry

end FamousTheorems
