-- Prove2me | Theorems.Thm_CorrelatedLocalSearch_eq_21_one_step
-- name    : CorrelatedLocalSearch.eq_21_one_step
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:19.507535+00:00
-- url     : https://prove2.me/theorems/691cb902-3895-454d-a5bc-6047933f7693
-- title:
--   (21) — one-step comparison $k^{-s_*}\sum_{a\text{ live}}f(\mathrm{pot}(wa))\le af(d-1)+bf(d+1)$
-- statement:
--   Let $k/2<r<k$ and consider a process satisfying the integer-potential hypotheses of Lemma C.1. Let $w$ be a surviving history of potential $d=\mathrm{pot}(w)$, and let $f:\mathbb N\to\mathbb R$ be nonnegative and nondecreasing with $f(0)=0$. Then
--   $$
--   k^{-s_*}\sum_{a\in[k]:\ wa\text{ live}} f\bigl(\mathrm{pot}(wa)\bigr)\ \le\ a\,f(d-1)+b\,f(d+1),
--   \qquad a=r\,k^{-s_*},\ b=(k-r)\,k^{-s_*}.
--   $$
--
--   This is the one-step inequality behind both halves of the barrier argument: it is applied to $H_m$ for first-hit prefixes and to $F_t$ for paths below the barrier.
--
--   Differences from the source:
--   - encoding: integers k/2 < r < k → natural numbers k, r with k < 2r and r < k; reason: same instances
--   - encoding: a deterministic process with live histories, a potential and a stopping time τ → a liveness predicate `live` and a potential `pot` on words; a history is live in the paper's sense when all its prefixes satisfy `live` (`Surv`); τ = hitTime live ∈ ℕ∞, ⊤ if it never stops; reason: every deterministic process driven by the tape is described this way, and conversely
--   - reading: f nonnegative and increasing → f nonnegative and nondecreasing (Monotone); reason: the paper applies (21) to F_t = (R^(m))^t 1, which starts as a constant vector, so 'increasing' means nondecreasing; this is the weaker hypothesis
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), App. C.1, proof of Lemma C.1, eq. (21), p.22 (PDF p.24)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_sStar
import Definitions.Def_CorrelatedLocalSearch_IsPotentialProcess

set_option autoImplicit false

open Classical

namespace CorrelatedLocalSearch

/-- The one-step comparison (21) (Xu, *Local Search with Correlated Randomness*,
arXiv:2607.17469 (sha256 17e00d69…), App. C.1, proof of Lemma C.1, eq. (21), p.22): for a
process satisfying the hypotheses of Lemma C.1 and a surviving history `w` of potential `d`,
and every nonnegative nondecreasing `f` with `f(0) = 0`,
`k^{−s∗} Σ_{a : w a live} f(pot(w a)) ≤ a f(d − 1) + b f(d + 1)`, with `a = r k^{−s∗}`,
`b = (k − r) k^{−s∗}`.

**Formalization Note** "Increasing" is read as nondecreasing (`Monotone`), the weaker
hypothesis. The live children are the symbols `a` with `live (w ++ [a])`; `d − 1` is natural
subtraction, harmless since `d ≥ 1`. -/
theorem eq_21_one_step (k r : ℕ) (hk : k < 2 * r) (hr : r < k)
    (live : List (Fin k) → Prop) (pot : List (Fin k) → ℕ) (h : ℕ)
    (hP : IsPotentialProcess k r live pot h) (w : List (Fin k)) (hw : Surv live w)
    (f : ℕ → ℝ) (hf0 : f 0 = 0) (hfnn : ∀ d, 0 ≤ f d) (hfmono : Monotone f) :
    (k : ℝ) ^ (-sStar k r) * ∑ a : Fin k, (if live (w ++ [a]) then f (pot (w ++ [a])) else 0) ≤
      (r : ℝ) * (k : ℝ) ^ (-sStar k r) * f (pot w - 1) +
        ((k : ℝ) - r) * (k : ℝ) ^ (-sStar k r) * f (pot w + 1) := by sorry

end CorrelatedLocalSearch
