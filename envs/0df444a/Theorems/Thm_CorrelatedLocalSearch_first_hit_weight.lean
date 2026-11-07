-- Prove2me | Theorems.Thm_CorrelatedLocalSearch_first_hit_weight
-- name    : CorrelatedLocalSearch.first_hit_weight
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:25.943382+00:00
-- url     : https://prove2.me/theorems/c7233be7-796f-4818-a399-4a45a1e48338
-- title:
--   Proof of Lemma C.1 — the weight of first-hit prefixes is at most $H_m(h)$
-- statement:
--   Let $k/2<r<k$ and consider a process satisfying the integer-potential hypotheses of Lemma C.1 with initial potential $h$. Let $m>h$ be an integer and $T\ge0$. Call a word $w$ a **first-hit prefix** if it survives, $\mathrm{pot}(w)\ge m$, and every proper prefix of $w$ has potential $<m$. Then
--   $$
--   \sum_{\substack{w \text{ first-hit},\ |w|\le T}} k^{-s_*|w|}\ \le\ H_m(h).
--   $$
--
--   This is the first of the two parts of the cover of $\{\tau>T\}$: the cost of covering the paths that reach the barrier.
--
--   **Formalization Note** A word of length $t$ is written `List.ofFn v` with $v:\mathrm{Fin}\,t\to\mathrm{Fin}\,k$; the sum runs over $t\le T$ and all such $v$.
--
--   Differences from the source:
--   - encoding: integers k/2 < r < k → natural numbers k, r with k < 2r and r < k; reason: same instances
--   - encoding: a deterministic process with live histories, a potential and a stopping time τ → a liveness predicate `live` and a potential `pot` on words; a history is live in the paper's sense when all its prefixes satisfy `live` (`Surv`); τ = hitTime live ∈ ℕ∞, ⊤ if it never stops; reason: every deterministic process driven by the tape is described this way, and conversely
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), App. C.1, proof of Lemma C.1, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_sStar
import Definitions.Def_CorrelatedLocalSearch_IsPotentialProcess
import Definitions.Def_CorrelatedLocalSearch_Hm

set_option autoImplicit false

open Classical

namespace CorrelatedLocalSearch

/-- The weight of first-hit prefixes (Xu, *Local Search with Correlated Randomness*,
arXiv:2607.17469 (sha256 17e00d69…), App. C.1, proof of Lemma C.1, p.22): for a process
satisfying the hypotheses of Lemma C.1 with initial potential `h`, a barrier `m > h` and a
horizon `T`, the sum of the powered prefix weights `k^{−s∗|w|}` over the first-hit prefixes —
words `w` of length at most `T` that survive, have `pot w ≥ m`, and whose proper prefixes all
have potential `< m` — is at most `H_m(h)`.

**Formalization Note** A word of length `t` is `List.ofFn v` for `v : Fin t → Fin k`; the sum
runs over `t ≤ T` and all such `v`. -/
theorem first_hit_weight (k r : ℕ) (hk : k < 2 * r) (hr : r < k)
    (live : List (Fin k) → Prop) (pot : List (Fin k) → ℕ) (h : ℕ)
    (hP : IsPotentialProcess k r live pot h) (m : ℕ) (hm : h < m) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), ∑ v : Fin t → Fin k,
        (if Surv live (List.ofFn v) ∧ m ≤ pot (List.ofFn v) ∧
            (∀ u : List (Fin k), u <+: List.ofFn v → u ≠ List.ofFn v → pot u < m)
          then (k : ℝ) ^ (-(sStar k r * t)) else 0) ≤ Hm k r m h := by sorry

end CorrelatedLocalSearch
