-- Prove2me | Theorems.Thm_ForecastComp_IELF_win_prob_transfer_mono
-- name    : ForecastComp.IELF.win_prob_transfer_mono
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:38.975975+00:00
-- url     : https://prove2.me/theorems/bdb8d2ad-2260-42de-8bfb-7fb7f1f881d3
-- title:
--   Proof of Theorem 6 (Appendix L), p. 34 — increasing E[F_{i,k}] cannot decrease the probability of winning overall
-- statement:
--   Let $n\ge2$ and let $q,q'$ be $m\times n$ tables of event-winner probabilities. Fix an event $k_0$, a forecaster $i$ and $\varepsilon\ge0$, and suppose that $q'$ differs from $q$ only on event $k_0$, where mass $\varepsilon$ moves to $i$ uniformly from all others:
--   $$q'_{k_0,i}=q_{k_0,i}+\varepsilon,\qquad q'_{k_0,j}=q_{k_0,j}-\frac{\varepsilon}{n-1}\quad(j\ne i),$$
--   and that $q_{l,j}\ge0$ for every event $l\ne k_0$ and every forecaster $j$. Then
--   $$\mathrm{winProb}(q,i)\le\mathrm{winProb}(q',i),$$
--   where $\mathrm{winProb}(q,i)=\sum_{w}\prod_k q_{k,w_k}\,\mathrm{tie}(w,i)$ is the probability that $i$ has the most event wins (ties broken uniformly at random) when the event winners $w_k$ are drawn independently with $\Pr(w_k=l)=q_{k,l}$.
--
--   Combined with the uniform-transfer property of ELF, this says that raising $i$'s expected winning probability on one event cannot lower $i$'s chance of winning overall.
-- source:
--   Witkowski et al., arXiv:2101.01816v2, p. 34, proof of Theorem 6 (Appendix L), end of second paragraph

import Mathlib
import Definitions.Def_ForecastComp_IELF_Model

namespace ForecastComp.IELF

/-- Proof of Theorem 6 (Appendix L), p. 34: with event winners drawn independently across events,
moving probability mass `ε ≥ 0` on event `k₀` toward forecaster `i`, taken uniformly
(`ε/(n−1)` each) from every other forecaster, cannot decrease `i`'s probability of being selected
by the most-wins rule with uniform tie-breaking. -/
theorem win_prob_transfer_mono {m n : ℕ} (hn : 2 ≤ n) (q q' : Fin m → Fin n → ℝ)
    (k₀ : Fin m) (i : Fin n) (ε : ℝ) (hε : 0 ≤ ε)
    (hother : ∀ l, l ≠ k₀ → q' l = q l)
    (hi : q' k₀ i = q k₀ i + ε)
    (hj : ∀ j, j ≠ i → q' k₀ j = q k₀ j - ε / ((n:ℝ) - 1))
    (hnonneg : ∀ l, l ≠ k₀ → ∀ j, 0 ≤ q l j) :
    winProbOf q i ≤ winProbOf q' i := by sorry

end ForecastComp.IELF
