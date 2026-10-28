-- Prove2me | Theorems.Thm_ForecastComp_IELF_win_prob_transfer_strict
-- name    : ForecastComp.IELF.win_prob_transfer_strict
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:35.96341+00:00
-- url     : https://prove2.me/theorems/e57ce1d0-3650-4035-8ec9-7c218b528043
-- title:
--   Proof of Theorem 6 (Appendix L), p. 34 — event k is pivotal with positive probability: strict increase
-- statement:
--   In the setting of the previous statement, assume moreover $\varepsilon>0$ and $q_{l,j}>0$ for every event $l\ne k_0$ and every forecaster $j$. Then
--   $$\mathrm{winProb}(q,i)<\mathrm{winProb}(q',i).$$
--   Event $k_0$ is pivotal for $i$ on some configuration of the other events' winners, and positivity of all other event-winner probabilities gives that configuration positive probability.
--
--   Positivity is where the requirement $R\in[0,1)$ for $m\ge2$ enters: with values strictly below $1$, every ELF winning probability is strictly positive (footnote 10 of the paper explains that strictness can fail otherwise).
-- source:
--   Witkowski et al., arXiv:2101.01816v2, p. 34, proof of Theorem 6 (Appendix L), third paragraph

import Mathlib
import Definitions.Def_ForecastComp_IELF_Model

namespace ForecastComp.IELF

/-- Proof of Theorem 6 (Appendix L), p. 34: if moreover `ε > 0` and every event winner
probability on the other events is strictly positive, the transfer toward `i` strictly increases
`i`'s probability of being selected (event `k₀` is pivotal with positive probability). -/
theorem win_prob_transfer_strict {m n : ℕ} (hn : 2 ≤ n) (q q' : Fin m → Fin n → ℝ)
    (k₀ : Fin m) (i : Fin n) (ε : ℝ) (hε : 0 < ε)
    (hother : ∀ l, l ≠ k₀ → q' l = q l)
    (hi : q' k₀ i = q k₀ i + ε)
    (hj : ∀ j, j ≠ i → q' k₀ j = q k₀ j - ε / ((n:ℝ) - 1))
    (hpos : ∀ l, l ≠ k₀ → ∀ j, 0 < q l j) :
    winProbOf q i < winProbOf q' i := by sorry

end ForecastComp.IELF
