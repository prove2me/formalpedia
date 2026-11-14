-- Prove2me | Theorems.Thm_BilateralProfit_lemma_4_6
-- name    : BilateralProfit.lemma_4_6
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T02:21:13.338329+00:00
-- url     : https://prove2.me/theorems/73af2496-b5ce-4cec-8bc4-4566940867da
-- title:
--   Lemma 4.6 — OneRound guarantee $\max_{a',v}\mathbb E[h_a(v,a')]\le (C_0+2)/K$
-- statement:
--   Let $K\ge1$ and let $C_0$ be a constant for which the information inequality of Theorem 4.2 holds at resolution $K$ for every distribution $\rho$ on $G_K\times\mathcal A$. Let $w$ be a probability vector on $\mathcal A$ with $w(a')\ge1/(|\mathcal A|(1+\beta K))$ for all $a'\in\mathcal A$, and let $(a,Q_0,Q_1)$ be the proposal returned by OneRound$(w)$. Then its score (6) satisfies
--   $$\max_{a'\in\mathcal A,\ v\in G_K}\mathbb E\big[h_a(v,a')\big]\le\frac{C_0+2}K,$$
--   the expectation being over the uniform draw $j^\star\in\{1,\dots,J\}$ of OneRound.
--
--   This is the per-round guarantee that the proof of Theorem 4.1 telescopes.
--
--   **Formalization Note** The score uses the returned $Q_0,Q_1$ and the input $w$; the expectation over $j^\star$ is the average over the $J$ draws; the maximum is a bound for every $(v,a')$.
--
--   Differences from the source:
--   - generalization: $C_0$ the universal constant of Theorem 4.2 → any $C_0$ for which Theorem 4.2's inequality holds at this $K$ for every $\rho$; reason: the universal $C_0$ is such a constant, so the paper's statement is the special case
--   - encoding: the grid $G_K$ of step size $1/K$ → hypothesis $0<K$; reason: the step size $1/K$ presupposes $K\ge1$ (Lemma A.6: "for every integer $K\ge1$")
--   - encoding: $\max_{a',v}\mathbb E[h_a(v,a')]$ over the randomness of OneRound → for every $(v,a')$, the average over $j\in\{0,\dots,J-1\}$ ($j^\star=j+1$) of the score of the returned proposal; reason: OneRound's only randomness is $j^\star$, uniform on $\{1,\dots,J\}$
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Lemma 4.6, p.21 (PDF 23), eq. (13); proof pp.21–22 (PDF 23–24)

import Mathlib
import Definitions.Def_BilateralProfit_OneRound

namespace BilateralProfit

/-- **Lemma 4.6 (OneRound guarantee)**, Brüstle, di Gregorio, Fusco, Leonardi (manuscript,
sha256 e91e8127…), p.21 (PDF 23), eq. (13).

Let `C0` be a constant for which the information inequality (Theorem 4.2) holds at resolution
`K`. Let `w` be a probability vector on `𝒜` with `w(a′) ≥ 1/(|𝒜|(1 + βK))` for all `a′`, and let
`(a, Q_0, Q_1)` be the proposal returned by `OneRound(w)`. Then for every `a′ ∈ 𝒜` and `v ∈ G_K`,
`E[h_a(v, a′)] ≤ (C0 + 2)/K`, the expectation being over the uniform draw `j⋆ ∈ {1, …, J}`.

**Formalization Note.** The score `h_a` is (6), computed from the returned `Q_0, Q_1` and the
input `w`. The expectation over `j⋆` is the average over `j : Fin J`. -/
theorem lemma_4_6 (K : ℕ) (hK : 0 < K) (C₀ : ℝ)
    (hC₀ : ∀ ρ : Grid K × Act K → ℝ, IsDist ρ →
      ∃ a : Act K, gap ρ a - beta K * info ρ a ≤ C₀ / K)
    (w : Act K → ℝ) (hw : IsDist w) (hwf : ∀ a', wFloor K ≤ w a') (v : Grid K) (a' : Act K) :
    (∑ j : Fin (Jpar K), hScore w (oneRoundVal K w j) v a') / Jpar K ≤ (C₀ + 2) / K := by sorry

end BilateralProfit
