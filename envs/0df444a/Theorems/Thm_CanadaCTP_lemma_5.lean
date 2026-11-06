-- Prove2me | Theorems.Thm_CanadaCTP_lemma_5
-- name    : CanadaCTP.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:19:35.307037+00:00
-- url     : https://prove2.me/theorems/562bb32e-27e3-423f-ac60-b04090ecfef6
-- title:
--   Lemma 5 — the ratio $\alpha/\beta$ on the first edge and on later edges
-- statement:
--   Let $X=(X_j)_{j\in[m]}$ with $m\ge1$, $\mathrm{coin}\in\mathrm{COIN}$, and $X'$, $\mathrm{coin}'$ as in Definition 8.
--
--   1. For every $x\in\operatorname{supp}X_1$ with $\beta(1,x,\mathrm{coin})>0$,
--   $$
--   \frac{\alpha(1,x,\mathrm{coin})}{\beta(1,x,\mathrm{coin})}=\frac{\mathrm{arrivalProb}(\mathrm{coin}')}{x+\mathrm{expCost}(\mathrm{coin}')}.
--   $$
--   2. For every $j\in\{2,\dots,m\}$ and $x\in\operatorname{supp}X_j$ with $\beta(j,x,\mathrm{coin})>0$,
--   $$
--   \frac{\alpha(j,x,\mathrm{coin})}{\beta(j,x,\mathrm{coin})}=\frac{\alpha(j,x,\mathrm{coin}')}{\beta(j,x,\mathrm{coin}')},
--   $$
--   where on the right $(j,x)$ is read as a pair of $X'$.
--
--   These identities drive the induction of Lemma 7.
--
--   **Formalization Note** The path is `Fin (n+1)`; the paper's edge $1$ is `0` and its edge $j\ge2$ is `j.succ`, which is edge `j` of $X'$. The budget $b$ of the printed statement does not occur and is omitted.
--
--   Differences from the source:
--   - encoding: m ≥ 1, edges 1, …, m, budget b ≥ 0 → X : Fin (n+1) → EdgeDist, edges 0, …, n; b omitted; reason: 0-based indexing; b does not occur in the conclusion
--   - encoding: arrivalProb(coin′), expCost(coin′), α, β → coinArr, coinCost, alphaC, betaC on tailDist X, tailCoin c; reason: Lemma 2 (item 1) identifies the closed formulas with the semantics
--   - encoding: independent non-negative discrete finitely supported edge weights given explicitly; edges and paths indexed from 1 → EdgeDist: an explicit list of (value, probability) pairs with distinct values, values ≥ 0, probabilities > 0 summing to 1; edges Fin m, paths Fin k, indexed from 0; reason: Lean convention; the list is exactly the support, so every instance of the paper is represented and nothing else
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Lemma 5, p.12; proof pp.12–13

import Mathlib
import Definitions.Def_CanadaCTP_PathOpt

namespace CanadaCTP

/-- Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33), Lemma 5, p.12: for a path with `m = n + 1 ≥ 1` edges and any `coin ∈ COIN`,
(1) for every `x ∈ supp(X₁)` with `β(1, x, coin) > 0`,
    `α(1, x, coin)/β(1, x, coin) = arrivalProb(coin′)/(x + expCost(coin′))`;
(2) for every later edge `j ∈ {2, …, m}` and `x ∈ supp(X_j)` with `β(j, x, coin) > 0`,
    `α(j, x, coin)/β(j, x, coin) = α(j, x, coin′)/β(j, x, coin′)` (edge `j` of `X` is edge `j − 1`
    of `X′`).

**Formalization Note.** Edges are 0-indexed: the paper's edge `1` is `0`, its edge `j ≥ 2` is
`j.succ` for `j : Fin n`, which is edge `j` of `X′ = tailDist X`. -/
theorem lemma_5 {n : ℕ} (X : Fin (n + 1) → EdgeDist) (c : Coin X) (hc : InCOIN X c) :
    (∀ x : Fin (X 0).pts.length, 0 < betaC X c 0 x →
      alphaC X c 0 x / betaC X c 0 x =
        coinArr (tailDist X) (tailCoin c) / (val X 0 x + coinCost (tailDist X) (tailCoin c))) ∧
    (∀ (j : Fin n) (x : Fin (X j.succ).pts.length), 0 < betaC X c j.succ x →
      alphaC X c j.succ x / betaC X c j.succ x =
        alphaC (tailDist X) (tailCoin c) j x / betaC (tailDist X) (tailCoin c) j x) := by sorry

end CanadaCTP
