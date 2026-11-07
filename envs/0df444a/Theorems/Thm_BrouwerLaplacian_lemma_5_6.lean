-- Prove2me | Theorems.Thm_BrouwerLaplacian_lemma_5_6
-- name    : BrouwerLaplacian.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:59:39.437815+00:00
-- url     : https://prove2.me/theorems/b162ee6f-ce01-4f24-b42d-1b1899c085ee
-- title:
--   Lemma 5.6 — $\sum_{i\ne j}(P_{ii}+P_{jj}-2P_{ij}-1)_+\le k(k+1)$, inequality (5.5)
-- statement:
--   Let $P$ be a real $n\times n$ orthogonal projection of rank $k$ with $P\mathbf 1=0$. Then
--
--   $$\sum_{i\ne j}\big(P_{ii}+P_{jj}-2P_{ij}-1\big)_+\le k(k+1),$$
--
--   where $(x)_+=\max(x,0)$.
--
--   It is the inequality from which the projection hypothesis of Lemma 5.1, and with it Brouwer's conjecture, is obtained.
--
--   **Formalization Note** $\sum_{i\ne j}$ runs over ordered pairs of distinct indices.
--
--   Differences from the source:
--   - reading: the lemma's second sentence "In particular, Lemma 3.2 implies Brouwer's Laplacian conjecture" → not a clause of this item; reason: it is a remark on the structure of the proof, carried by the goal theorem together with Lemma 3.2 and Lemma 5.1, not a mathematical statement about $P$
--   - encoding: indices $1,\dots,n$ → $\mathrm{Fin}\,n=\{0,\dots,n-1\}$; reason: relabeling; same instances
-- source:
--   P. K. Kothari, S. Tudose, On Brouwer's Laplacian conjecture, arXiv:2606.12197v1, Lemma 5.6, p.7, eq. (5.5) (proof p.8)

import Mathlib
import Definitions.Def_BrouwerLaplacian_IsOrthProj

namespace BrouwerLaplacian

open Finset Matrix

/-- **Lemma 5.6, inequality (5.5).**
Kothari, Tudose, *On Brouwer's Laplacian conjecture*, arXiv:2606.12197v1, Lemma 5.6, p.7:
"For any orthogonal projection P of rank k which satisfies P1 = 0, the following holds
Σ_{i≠j} (Pᵢᵢ + Pⱼⱼ − 2Pᵢⱼ − 1)₊ ≤ k(k + 1). (5.5)"

**Formalization Note.** `Σ_{i≠j}` is over ordered pairs of distinct indices; the positive part
`(x)₊` is `max x 0`. -/
theorem lemma_5_6 {n k : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) :
    ∑ i, ∑ j with i ≠ j, max (P i i + P j j - 2 * P i j - 1) 0
      ≤ (k : ℝ) * ((k : ℝ) + 1) := by sorry

end BrouwerLaplacian
