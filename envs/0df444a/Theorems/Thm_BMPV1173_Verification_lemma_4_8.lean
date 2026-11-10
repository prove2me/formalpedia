-- Prove2me | Theorems.Thm_BMPV1173_Verification_lemma_4_8
-- name    : BMPV1173.Verification.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:04:06.3558+00:00
-- url     : https://prove2.me/theorems/eba6f376-2e0b-40f6-a323-37b2db2b0b88
-- title:
--   Lemma 4.8 — general preprocessing bounds
-- statement:
--   Use the first-intersection neighborhoods, independent pivot and degree draws, and the covered/heavy definitions of (4.12)–(4.15). Every common one of $x_i,x_j$ belongs to $\mathrm{Coords}_{ij}$ for any choices of covered and heavy sets. For $1\le s,t\le n$, a sufficiently large absolute degree-sampling constant gives probability at least $0.98$ that all the following hold simultaneously:
--   $$i\in\mathrm{Heavy}_k\Rightarrow |N_k(i)\setminus\mathrm{Covered}_k|>t,\qquad i\notin\mathrm{Heavy}_k\Rightarrow |N_k(i)\setminus\mathrm{Covered}_k|\le4t,$$
--   $$\sum_i|\mathrm{Left}_i|\le\frac{100n^3}{st},\quad |\mathrm{Right}_j|\le s,\quad \sum_{j\ne i}|\{k\in\mathrm{Remaining}_{ij}:k\le\mathrm{first}(i,j)\}|\le4nt.$$
--   The lists and neighborhoods are computed from the arbitrary input and sampled draws. Coverage is deterministic; the probability refers to the complete joint event, including its prefix cutoff.
--
--   Differences from the source:
--   - encoding: bit entries indexed by [n] → Boolean functions on Fin n, with a matrix selector when needed; reason: the index bijection preserves every bit and every input instance
--   - encoding: independent uniform samples with replacement and sufficiently large absolute sampling constants → uniform probability on ordered draw tuples and ceiling lengths c(n/t)(1+log n); reason: ordered tuples keep every repeated occurrence, and the positive-dimension boundary is defined without changing the asymptotic sampling scale
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, Lemma 4.8, printed p.28 = PDF p.28.

import Definitions.Def_BMPV1173_Verification_Preprocessing

namespace BMPV1173.Verification

open scoped BigOperators

/-- General preprocessing, including deterministic coverage for arbitrary C,H,
and the full simultaneous probability-0.98 event. Source pp.27–28. -/
theorem lemma_4_8 :
    (∀ (n : ℕ) (x : VectorInput n) (C H : Fin n → Finset (Fin n)) (i j k : Fin n),
      x (i,k) = true → x (j,k) = true → k ∈ coordsFor x C H i j) ∧
    ∃ c : ℕ, 0 < c ∧ ∀ (n s t : ℕ), 1 ≤ n → 1 ≤ s → s ≤ n → 1 ≤ t → t ≤ n →
      ∀ x : VectorInput n,
      uniformProbability (fun z : (Fin s → Fin n) × (Fin (sampleCount c n t) → Fin n) =>
        preprocessingGood x z.1 z.2 t) ≥ 98 / 100 := by sorry

end BMPV1173.Verification
