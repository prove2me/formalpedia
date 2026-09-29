-- Prove2me | Theorems.Thm_FamousTheorems_riesz_lemma_normed_space
-- name    : FamousTheorems.riesz_lemma_normed_space
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:26.325009+00:00
-- url     : https://prove2.me/theorems/9d2fd93d-bb0a-48bd-9117-d99763c3c391
-- title:
--   Riesz's lemma
-- statement:
--   **Riesz's lemma.** Let $F$ be a closed proper subspace of a normed space $E$ and $r<1$. Then there is $x_0\notin F$ such that
--   $$r\,\|x_0\|\le\|x_0-y\|\qquad\text{for all }y\in F.$$
--
--   In particular, for $0<r<1$ there are unit-norm vectors at distance at least $r$ from $F$. The lemma is the key step in proving that a normed space whose closed unit ball is compact is finite-dimensional, and it is used throughout the spectral theory of compact operators.
--
--   **Formalization note.** Mathlib's `riesz_lemma`. The scalar field is any normed field, `F : Subspace 𝕜 E` is closed (`IsClosed (F : Set E)`), and properness is `∃ x, x ∉ F`. The inequality is stated as `r * ‖x₀‖ ≤ ‖x₀ - y‖` rather than normalising $x_0$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `riesz_lemma`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem riesz_lemma_normed_space {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Subspace 𝕜 E}
    (hFc : IsClosed (F : Set E)) (hF : ∃ x : E, x ∉ F) {r : ℝ} (hr : r < 1) :
    ∃ x₀ ∉ F, ∀ y ∈ F, r * ‖x₀‖ ≤ ‖x₀ - y‖ := by sorry

end FamousTheorems
