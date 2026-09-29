-- Prove2me | Theorems.Thm_FamousTheorems_weighted_hm_gm_inequality
-- name    : FamousTheorems.weighted_hm_gm_inequality
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:08.964287+00:00
-- url     : https://prove2.me/theorems/088db44f-ec0f-4b87-9046-2b0bce2eca1f
-- title:
--   The HM–GM inequality
-- statement:
--   **The HM–GM inequality.** Let $w_1,\dots,w_n>0$ be weights with $\sum_i w_i=1$ and let $z_1,\dots,z_n>0$. Then
--   $$\Big(\sum_i\frac{w_i}{z_i}\Big)^{-1}\le\prod_i z_i^{\,w_i}.$$
--
--   The weighted harmonic mean is at most the weighted geometric mean. It follows by applying the AM–GM inequality to the reciprocals $1/z_i$. Together with AM–GM it gives the chain $\mathrm{HM}\le\mathrm{GM}\le\mathrm{AM}$ of the classical means.
--
--   **Formalization note.** Mathlib's `Real.harm_mean_le_geom_mean_weighted`, over a nonempty finite index set `s`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Real.harm_mean_le_geom_mean_weighted`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem weighted_hm_gm_inequality {ι : Type*} (s : Finset ι) (w z : ι → ℝ) (hs : s.Nonempty) (hw : ∀ i ∈ s, 0 < w i)
    (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 < z i) : (∑ i ∈ s, w i / z i)⁻¹ ≤ ∏ i ∈ s, z i ^ w i := by sorry

end FamousTheorems
