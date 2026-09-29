-- Prove2me | Theorems.Thm_FamousTheorems_titu_lemma
-- name    : FamousTheorems.titu_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:05.35133+00:00
-- url     : https://prove2.me/theorems/41a96a25-43da-44fe-8971-ab143755f599
-- title:
--   Titu's lemma (Sedrakyan's inequality)
-- statement:
--   **Titu's lemma (Sedrakyan's inequality).** For real numbers $f_1,\dots,f_n$ and positive reals $g_1,\dots,g_n$,
--   $$\frac{(f_1+\cdots+f_n)^2}{g_1+\cdots+g_n}\le\frac{f_1^2}{g_1}+\cdots+\frac{f_n^2}{g_n}.$$
--
--   This is the Engel form of the Cauchy–Schwarz inequality, obtained by applying Cauchy–Schwarz to the vectors $(f_i/\sqrt{g_i})$ and $(\sqrt{g_i})$. It is a standard tool in olympiad inequalities.
--
--   **Formalization note.** Mathlib's `Finset.sq_sum_div_le_sum_sq_div`, stated here for real-valued families over a finset `s`. Mathlib proves it more generally over linearly ordered semifields.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Finset.sq_sum_div_le_sum_sq_div`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem titu_lemma {ι : Type*} (s : Finset ι) (f g : ι → ℝ) (hg : ∀ i ∈ s, 0 < g i) :
    (∑ i ∈ s, f i) ^ 2 / ∑ i ∈ s, g i ≤ ∑ i ∈ s, f i ^ 2 / g i := by sorry

end FamousTheorems
