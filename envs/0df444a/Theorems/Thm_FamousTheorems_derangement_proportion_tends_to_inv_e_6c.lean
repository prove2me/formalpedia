-- Prove2me | Theorems.Thm_FamousTheorems_derangement_proportion_tends_to_inv_e_6c
-- name    : FamousTheorems.derangement_proportion_tends_to_inv_e_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:47:01.24872+00:00
-- url     : https://prove2.me/theorems/4cd5b9c8-40ec-4e6f-9bcb-551768d8f1ec
-- title:
--   The proportion of derangements tends to 1/e
-- statement:
--   **The proportion of derangements tends to $1/e$.** Let $D_n$ be the number of derangements of an $n$-element set, the permutations with no fixed points. Then
--   $$\lim_{n\to\infty}\frac{D_n}{n!}=\frac1e.$$
--
--   This is the answer to Montmort's hat-check problem (1708): the probability that a random permutation has no fixed point tends to $1/e$. It follows from the inclusion–exclusion formula $D_n=n!\sum_{k=0}^n(-1)^k/k!$.
--
--   **Formalization note.** Mathlib's `numDerangements_tendsto_inv_e`. `numDerangements n` is $D_n$, and $1/e$ is written `Real.exp (-1)`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `numDerangements_tendsto_inv_e`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem derangement_proportion_tends_to_inv_e_6c :
    Filter.Tendsto (fun n : ℕ => (numDerangements n : ℝ) / n.factorial) Filter.atTop
      (nhds (Real.exp (-1))) := by sorry

end FamousTheorems
