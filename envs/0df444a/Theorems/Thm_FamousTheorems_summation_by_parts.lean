-- Prove2me | Theorems.Thm_FamousTheorems_summation_by_parts
-- name    : FamousTheorems.summation_by_parts
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:05:09.886363+00:00
-- url     : https://prove2.me/theorems/e86ed0e6-b6ab-41ed-84d5-256a0f8f7d8b
-- title:
--   Summation by parts (Abel's lemma)
-- statement:
--   **Summation by parts (Abel's lemma).** Let $f_i$ be scalars in a ring $R$ and $g_i$ vectors in an $R$-module, and write $G_k=\sum_{j<k}g_j$. For $m<n$,
--   $$\sum_{i=m}^{n-1}f_ig_i=f_{n-1}G_n-f_mG_m-\sum_{i=m}^{n-2}(f_{i+1}-f_i)\,G_{i+1}.$$
--
--   This is the discrete analogue of integration by parts. It is the key identity behind the Abel and Dirichlet tests for convergence of series, Abel's theorem on power series at the boundary, and many estimates in analytic number theory for sums weighted by arithmetic functions.
--
--   **Formalization note.** Mathlib's `Finset.sum_Ico_by_parts`. Sums over `Finset.Ico m n` run over $m\le i<n$ and `Finset.range k` over $j<k$. The scalars act on the module by `•`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Finset.sum_Ico_by_parts`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem summation_by_parts {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (f : ℕ → R) (g : ℕ → M) {m n : ℕ}
    (hmn : m < n) :
    ∑ i ∈ Finset.Ico m n, f i • g i =
      f (n - 1) • ∑ i ∈ Finset.range n, g i - f m • ∑ i ∈ Finset.range m, g i -
        ∑ i ∈ Finset.Ico m (n - 1), (f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), g j := by sorry

end FamousTheorems
