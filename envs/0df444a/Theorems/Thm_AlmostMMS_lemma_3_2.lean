-- Prove2me | Theorems.Thm_AlmostMMS_lemma_3_2
-- name    : AlmostMMS.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:50:38.81884+00:00
-- url     : https://prove2.me/theorems/a3991fb5-6fe0-452d-9b7c-dc545c9f9f2c
-- title:
--   Lemma 3.2 — the fractional MMS head profiles fit
-- statement:
--   For the fractional MMS head profiles $(x^*,\Pi)$:
--
--   1. $I(x^*,\Pi)=d$;
--   2. $H(x^*,\Pi,\ell)\le\ell-\frac1n\sum_{i\in N}(\ell-h_i)_+$ for every $0\le\ell\le m$;
--   3. $\sum_{j=1}^d\Delta(\pi_{i,j})\le(1-1/q)T_i$ for every $i\in N$;
--   4. $T(x^*,\Pi,\ell)\le\frac{1-1/q}{n}\sum_{i\in N}(\ell-h_i)_+$ for every $0\le\ell\le m$.
--
--   The factor $1-1/q$ in the tail load is the slack that later absorbs the factor $\lambda$ of the rounding.
--
--   Differences from the source:
--   - generalization: standing 1 ≤ d ≤ (1 − ε)n → 1 ≤ d ≤ n; reason: the lemma needs only that x* has weights ≥ 0; (1 − ε)n ≤ n
--   - encoding: §§3–5's standing ordered instance with MMS bundles of value 1 → a structure `J : OrderedInstance n m d`; reason: the structure holds exactly Assumption 1's three bullets
--   - encoding: (ℓ − h_i)₊ → truncated natural subtraction cast to ℝ; reason: the two agree on ℕ
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Lemma 3.2, p.23

import Mathlib
import Definitions.Def_AlmostMMS_OrderedInstance
import Definitions.Def_AlmostMMS_headCount
import Definitions.Def_AlmostMMS_deficit
import Definitions.Def_AlmostMMS_mmsProfileIn
import Definitions.Def_AlmostMMS_fracH
import Definitions.Def_AlmostMMS_xStar

namespace AlmostMMS

open Finset

/-- **Lemma 3.2, p.23.** Feige, Grinberg, *Almost-MMS allocations with small agent redundancy*, STOC 2027 submission,
arXiv:2611.05360 (manuscript sha256 3925c4ab…): for the fractional MMS head profiles `(x*, Π)`: `I(x*, Π) = d`;
`H(x*, Π, ℓ) ≤ ℓ - (1/n) ∑_{i ∈ N} (ℓ - h_i)₊`; `∑_{j=1}^d Δ(π_{i,j}) ≤ (1 - 1/q) T_i`; and
`T(x*, Π, ℓ) ≤ ((1 - 1/q)/n) ∑_{i ∈ N} (ℓ - h_i)₊`, for every `0 ≤ ℓ ≤ m` and every `i ∈ N`.

**Formalization Note.** Of the standing `1 ≤ d ≤ (1 - ε) n` only `1 ≤ d ≤ n` is assumed. -/
theorem lemma_3_2 {n m d q : ℕ} (hq : 3 ≤ q) (hd : 1 ≤ d) (hdn : d ≤ n)
    (J : OrderedInstance n m d) :
    fracI (mmsProfileSet J q) (xStar J q) = (d : ℝ) ∧
    (∀ ℓ ≤ m, fracH J.v (mmsProfileSet J q) (xStar J q) ℓ ≤
      (ℓ : ℝ) - (1 / (n : ℝ)) * ∑ i, ((ℓ - headCount J.v q i : ℕ) : ℝ)) ∧
    (∀ i, ∑ j : Fin d, deficit q (mmsProfile J q i j) ≤ (1 - 1 / (q : ℝ)) * tailVal J.v q i) ∧
    (∀ ℓ ≤ m, fracT J.v q (mmsProfileSet J q) (xStar J q) ℓ ≤
      ((1 - 1 / (q : ℝ)) / (n : ℝ)) * ∑ i, ((ℓ - headCount J.v q i : ℕ) : ℝ)) := by sorry

end AlmostMMS
