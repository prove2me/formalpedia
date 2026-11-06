-- Prove2me | Theorems.Thm_CanadaCTP_lemma_4
-- name    : CanadaCTP.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:20:35.301103+00:00
-- url     : https://prove2.me/theorems/80b30626-852f-4be6-b184-658eb4ea4577
-- title:
--   Lemma 4 — under correctness, PathExplorer on $(X,0)$ traces the linear pieces of $\mathrm{prob}_X$
-- statement:
--   Let $X$ be the weights of a path, and assume PathExplorer is correct: for every $b\ge0$ its output is a coin vector with expected cost at most $b$ and arrival probability $\mathrm{prob}_X(b)$. Run it on $(X,0)$; let $T$ be the number of iterations, $\mathrm{coin}_i$ the strategy before iteration $i$, $(j_i,x_i)$ the pair set to $0$ there, $b_i=\mathrm{expCost}(\mathrm{coin}_i)$, and $b_{T+1}$ the expected cost of the output. Then:
--
--   1. $b_1>b_2>\dots>b_{T+1}=0$;
--   2. for every $i\le T$ and $y\in[b_{i+1},b_i]$,
--   $$
--   \mathrm{prob}_X(y)=\mathrm{prob}_X(b_{i+1})+(y-b_{i+1})\,\frac{\alpha(j_i,x_i,\mathrm{coin}_i)}{\beta(j_i,x_i,\mathrm{coin}_i)},
--   $$
--   and $\mathrm{prob}_X(y)=1$ for $y\ge b_1$;
--   3. $T\le d=\sum_j|\operatorname{supp}X_j|$, so $\mathrm{prob}_X$ has at most $d+1$ breakpoints $(b_i,\mathrm{arrivalProb}(\mathrm{coin}_i))$.
--
--   This is how SumMaximizer obtains the segments of every $\mathrm{prob}_{X^i}$.
--
--   **Formalization Note** Indices start at $0$: `bs 0` is $b_1$ and `bs T` is $b_{T+1}$. The hypothesis is the printed assumption, in the form of Lemma 7's conclusion, which discharges it.
--
--   Differences from the source:
--   - encoding: b_1, …, b_{T+1}, coin_1, …, coin_T → bs 0, …, bs T and the trace entries 0, …, T−1; reason: 0-based indexing
--   - reading: (3) prob_X has at most d + 1 breakpoints → T ≤ d; reason: the proof (p.11) counts the breakpoints (b_i, arrivalProb(coin_i)) of (2), T + 1 of them; with (2), T ≤ d implies the printed bound
--   - encoding: expCost(coin_i) = b_i, slopes α/β of coin strategies → the closed formulas coinCost, alphaC, betaC; reason: Lemma 2 (item 1) identifies them with the semantics
--   - encoding: "assume PathExplorer correctly calculates an optimal coin_X(b) for every b ≥ 0" → hypothesis: for every b ≥ 0, peOut X b ∈ COIN, its expected cost is ≤ b and its arrival probability is prob_X(b); reason: the printed hypothesis, stated as Lemma 7 states correctness
--   - encoding: probabilities and expected values of the whole (possibly unbounded) run → suprema over the horizon N of the N-step quantities, in ℝ≥0∞; reason: the events are absorbing and the costs non-decreasing in N, so the suprema are the limits, i.e. the same values
--   - encoding: independent non-negative discrete finitely supported edge weights given explicitly; edges and paths indexed from 1 → EdgeDist: an explicit list of (value, probability) pairs with distinct values, values ≥ 0, probabilities > 0 summing to 1; edges Fin m, paths Fin k, indexed from 0; reason: Lean convention; the list is exactly the support, so every instance of the paper is represented and nothing else
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Lemma 4, p.10; proof pp.10–11

import Mathlib
import Definitions.Def_CanadaCTP_PathExplorer

namespace CanadaCTP

/-- Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33), Lemma 4, p.10 (proof pp.10–11): assuming PathExplorer is correct for every budget,
its run on `(X, 0)` describes `prob_X` exactly.

With the trace of the run on `(X, 0)` (`T` iterations, `coin_i` the strategy before iteration
`i`, `(j_i, x_i)` the pair set to `0` there) and `b_i = expCost(coin_i)` (indices from `0`
here, so `b 0` is the paper's `b₁` and `b T` its `b_{T+1}`, the cost of the output):
(1) `b 0 > b 1 > ⋯ > b T = 0`;
(2) on `[b (i+1), b i]` the function `prob_X` is linear with slope `α(j_i, x_i, coin_i)/β(j_i, x_i, coin_i)`,
    and it equals `1` on `[b 0, ∞)`;
(3) `T ≤ d`, i.e. the breakpoints `(b_i, arrivalProb(coin_i))` are at most `d + 1`.

**Formalization Note.** The hypothesis is the printed one ("PathExplorer correctly calculates
an optimal `coin_X(b)` for every `b ≥ 0`"), in the form of Lemma 7's conclusion. Expected costs of
coin strategies are the closed formula `coinCost` (Lemma 2). -/
theorem lemma_4 {m : ℕ} (X : Fin m → EdgeDist)
    (hcorr : ∀ b : ℝ, 0 ≤ b → InCOIN X (peOut X b) ∧
      expCost (pathInst X) (coinPolicy X (peOut X b)) ≤ ENNReal.ofReal b ∧
      (arrProb (pathInst X) (coinPolicy X (peOut X b))).toReal = probX X b) :
    let tr := peTrace X 0
    let bs : ℕ → ℝ := fun i =>
      if h : i < tr.length then coinCost X (tr.get ⟨i, h⟩).coin else coinCost X (peOut X 0)
    ((∀ i j : ℕ, i < j → j ≤ tr.length → bs j < bs i) ∧ bs tr.length = 0) ∧
    (∀ (i : ℕ) (h : i < tr.length), ∀ y ∈ Set.Icc (bs (i + 1)) (bs i),
      probX X y = probX X (bs (i + 1)) + (y - bs (i + 1)) *
        (alphaC X (tr.get ⟨i, h⟩).coin (tr.get ⟨i, h⟩).pair.1 (tr.get ⟨i, h⟩).pair.2 /
          betaC X (tr.get ⟨i, h⟩).coin (tr.get ⟨i, h⟩).pair.1 (tr.get ⟨i, h⟩).pair.2)) ∧
    (∀ y : ℝ, bs 0 ≤ y → probX X y = 1) ∧
    tr.length ≤ dX X := by sorry

end CanadaCTP
