-- Prove2me | Theorems.Thm_FamousTheorems_rearrangement_inequality
-- name    : FamousTheorems.rearrangement_inequality
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:46.458708+00:00
-- url     : https://prove2.me/theorems/69dd93d5-72fa-4139-8f1a-d26530eefb06
-- title:
--   The rearrangement inequality
-- statement:
--   **The rearrangement inequality.** Let $f,g:\iota\to\mathbb R$ on a finite index set be similarly ordered (monovarying: $g(i)<g(j)\Rightarrow f(i)\le f(j)$). Then for every permutation $\sigma$ of $\iota$,
--   $$\sum_i f(i)\,g(\sigma(i))\le\sum_i f(i)\,g(i).$$
--
--   So a sum of products is largest when the two sequences are sorted in the same order. The inequality gives short proofs of AM–GM, Chebyshev's sum inequality and many olympiad inequalities.
--
--   **Formalization note.** Mathlib's `Monovary.sum_mul_comp_perm_le_sum_mul`, the real-valued, full-index-set case of `MonovaryOn.sum_smul_comp_perm_le_sum_smul`. `Monovary f g` means `g i < g j → f i ≤ f j`, which covers ties in either sequence.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Monovary.sum_mul_comp_perm_le_sum_mul`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem rearrangement_inequality {ι : Type*} [Fintype ι] {f g : ι → ℝ} (hfg : Monovary f g) (σ : Equiv.Perm ι) :
    ∑ i, f i * g (σ i) ≤ ∑ i, f i * g i := by sorry

end FamousTheorems
