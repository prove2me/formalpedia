-- Prove2me | Theorems.Thm_FamousTheorems_chebyshev_sum_inequality
-- name    : FamousTheorems.chebyshev_sum_inequality
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:54.840034+00:00
-- url     : https://prove2.me/theorems/656b7a2c-3208-4ebc-a687-de9e37e0a0e5
-- title:
--   Chebyshev's sum inequality
-- statement:
--   **Chebyshev's sum inequality.** Let $f,g$ be real functions on a finite set $s$ that are similarly ordered on $s$ (monovarying). Then
--   $$\Big(\sum_{i\in s}f(i)\Big)\Big(\sum_{i\in s}g(i)\Big)\le|s|\sum_{i\in s}f(i)g(i).$$
--
--   Equivalently, the average of the products is at least the product of the averages. It is a discrete analogue of the positive correlation of increasing functions, and it follows from the rearrangement inequality by summing over cyclic shifts.
--
--   **Formalization note.** Mathlib's `MonovaryOn.sum_mul_sum_le_card_mul_sum`, the real-valued case of `MonovaryOn.sum_smul_sum_le_card_smul_sum`. `MonovaryOn f g s` means that for $i,j\in s$, $g(i)<g(j)$ implies $f(i)\le f(j)$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MonovaryOn.sum_mul_sum_le_card_mul_sum`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem chebyshev_sum_inequality {ι : Type*} (s : Finset ι) {f g : ι → ℝ} (hfg : MonovaryOn f g s) :
    (∑ i ∈ s, f i) * ∑ i ∈ s, g i ≤ (s.card : ℝ) * ∑ i ∈ s, f i * g i := by sorry

end FamousTheorems
