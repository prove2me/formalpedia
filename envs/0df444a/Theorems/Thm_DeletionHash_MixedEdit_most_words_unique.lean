-- Prove2me | Theorems.Thm_DeletionHash_MixedEdit_most_words_unique
-- name    : DeletionHash.MixedEdit.most_words_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:41:57.416406+00:00
-- url     : https://prove2.me/theorems/88104b73-f5bc-442d-9a8a-1e83636d0f44
-- title:
--   Lemma 2.1 — most words unique
-- statement:
--   Let $\Sigma$ be an arbitrary finite alphabet of size $q\ge2$, let $n\ge1$ and set $k=2\lceil\log_q n\rceil+2$. Then the full chain is
--   $$|W_{n,k}|\ge\bigl(1-\tbinom n2 q^{-k}\bigr)q^n\ge\tfrac78 q^n\ge q^n/2.$$
--   The combinatorial factor is $\binom n2$. Uniqueness compares every pair of valid windows, including overlapping ones. This supplies the constant fraction of words needed for selecting the code.
--
--   Differences from the source:
--   - encoding: positive word length implicit in log_q n → an explicit hypothesis n≥1 and a natural ceiling; reason: the logarithm is defined on this domain and the natural ceiling equals the ordinary ceiling for log_q n≥0
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), Lemma 2.1, printed p. 5 (PDF p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_UniqueWords

namespace DeletionHash.MixedEdit

universe u

/-- Lemma 2.1 with its complete chain, including the binomial numerator n and 7/8. -/
theorem most_words_unique {α : Type u} [Fintype α] [DecidableEq α]
    (n : ℕ) (hn : 1 ≤ n) (hq : 2 ≤ Fintype.card α) :
    let q := Fintype.card α
    let k := uniqueLength q n
    let B := (1 - (n.choose 2 : ℝ) / (q : ℝ)^k) * (q : ℝ)^n
    (B ≤ ((uniqueFamily α n k).card : ℝ)) ∧
    ((7:ℝ)/8 * (q : ℝ)^n ≤ B) ∧ ((q : ℝ)^n/2 ≤ (7:ℝ)/8 * (q : ℝ)^n) := by sorry

end DeletionHash.MixedEdit
