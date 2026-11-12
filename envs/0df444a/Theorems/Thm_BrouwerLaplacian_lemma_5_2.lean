-- Prove2me | Theorems.Thm_BrouwerLaplacian_lemma_5_2
-- name    : BrouwerLaplacian.lemma_5_2
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T16:59:38.171212+00:00
-- url     : https://prove2.me/theorems/e4b7c3c4-c1fa-4619-b7a8-f85e16e24da5
-- title:
--   Lemma 5.2 — projection identity (5.1)
-- statement:
--   Let $P$ be a real $n\times n$ orthogonal projection of rank $k$ with $P\mathbf 1=0$. Then
--
--   $$\frac14\sum_{i\ne j}\Big[(P_{ii}+P_{jj}-2P_{ij})^2-(P_{ii}-P_{jj})^2\Big]=k(k+1).$$
--
--   This exact identity converts the positive-part sum of Lemma 5.6 into the quadratic inequality (5.6).
--
--   **Formalization Note** $\sum_{i\ne j}$ runs over ordered pairs of distinct indices.
--
--   Differences from the source:
--   - encoding: indices $1,\dots,n$ → $\mathrm{Fin}\,n=\{0,\dots,n-1\}$; reason: relabeling; same instances
-- source:
--   P. K. Kothari, S. Tudose, On Brouwer's Laplacian conjecture, arXiv:2606.12197v1, Lemma 5.2, p.5, eq. (5.1)

import Mathlib
import Definitions.Def_BrouwerLaplacian_IsOrthProj

namespace BrouwerLaplacian

open Finset Matrix

/-- **Lemma 5.2 (A Projection Identity), identity (5.1).**
Kothari, Tudose, *On Brouwer's Laplacian conjecture*, arXiv:2606.12197v1, Lemma 5.2, p.5:
"For any orthogonal projection P of rank k which satisfies P1 = 0, the following holds
1/4 Σ_{i≠j} [(Pᵢᵢ + Pⱼⱼ − 2Pᵢⱼ)² − (Pᵢᵢ − Pⱼⱼ)²] = k(k + 1). (5.1)"

**Formalization Note.** `Σ_{i≠j}` is over ordered pairs of distinct indices of `Fin n`. -/
theorem lemma_5_2 {n k : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) :
    (1 / 4 : ℝ) * ∑ i, ∑ j with i ≠ j,
        ((P i i + P j j - 2 * P i j) ^ 2 - (P i i - P j j) ^ 2)
      = (k : ℝ) * ((k : ℝ) + 1) := by sorry

end BrouwerLaplacian
