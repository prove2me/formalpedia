-- Prove2me | Theorems.Thm_AnalystRanking_Revelation_lemma_1_benchmark_most_informative
-- name    : AnalystRanking.Revelation.lemma_1_benchmark_most_informative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:43:42.084238+00:00
-- url     : https://prove2.me/theorems/63c6feb1-123d-4e4f-bbcb-6a81abb1e3c1
-- title:
--   Lemma 1: most informative benchmark equilibrium (corrected: $q\in[1-\gamma,\gamma]$)
-- statement:
--   In the benchmark of §3.1 each analyst maximizes his own expected accuracy payoff ($W>0$ for a correct forecast, $0$ otherwise). Let $\gamma\in(\tfrac12,1)$ and $q\in(0,1)$. Then the most informative benchmark equilibrium (Definition 2) is characterized as follows:
--
--   1. if $1-\gamma\le q\le\gamma$, it is the separating strategy $\sigma^h=1=\sigma^l$;
--   2. if $q<1-\gamma$ or $q>\gamma$, it exists and is pooling, $\sigma^h=1-\sigma^l$.
--
--   This is the benchmark against which Proposition 5 measures the effect of competition: its informativeness $\Pi_B$ is positive exactly on $[1-\gamma,\gamma]$.
--
--   Differences from the source:
--   - correction: i) σh = 1 = σl at q ∈ [γ, 1 − γ] → 1 − γ ≤ q ≤ γ; reason: for γ > 1/2 the printed interval is empty; the derivation on p. 10 ('q ≤ γ', 'q ≥ 1 − γ', 'at q ∈ [1 − γ, γ], there exists a separating equilibrium') and part ii) give [1 − γ, γ]
--   - reading: ℰ = the set of all equilibria (Definition 2), with symmetric equilibria and σh ⩾ 1 − σl (p. 9) → IsCompEq / IsBenchEq: symmetric σ ∈ [0,1]² with σh ≥ 1 − σl, each signal type best-responding against every mixed deviation, Bayes beliefs; reason: the paper restricts attention to these profiles on p. 9 and calls them the equilibria
--   - encoding: strategies (σh, σl), {h,l}, {ĥ,l̂}, {H,L} → σ : ℝ × ℝ, Bool with true the high value; reason: Lean convention; same instances
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Lemma 1, p. 11

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_IsBenchEq
import Definitions.Def_AnalystRanking_Revelation_IsMostInformative

namespace AnalystRanking.Revelation

/-- **Lemma 1 (Benchmark), interval corrected.**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Lemma 1, p. 11: "If the objective of an analyst is to maximize his own forecast accuracy
without any concern about relative ranking, then the most informative equilibrium is
characterized as follows: i) `σʰ = 1 = σˡ` at `q ∈ [γ, 1 − γ]` and ii) `σʰ = 1 − σˡ` at
`q ∈ (0, 1 − γ) ∪ (γ, 1)`."

**Formalization Note.** Correction: the printed interval `[γ, 1 − γ]` is empty for `γ > 1/2`; the
derivation on p. 10 ("forecasts low if … `q ≤ γ` … forecasts high if … `q ≥ 1 − γ`. As such, at
`q ∈ [1 − γ, γ]`, there exists a separating equilibrium") and part ii) give `[1 − γ, γ]`. Standing
assumptions: `γ ∈ (1/2, 1)`, `q ∈ (0, 1)` (§2) and `W > 0` (§3.1). -/
theorem lemma_1_benchmark_most_informative (W q γ : ℝ) (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1)
    (hq0 : 0 < q) (hq1 : q < 1) (hW : 0 < W) :
    (1 - γ ≤ q → q ≤ γ → IsMostInformative (IsBenchEq W q γ) (1, 1)) ∧
    (q < 1 - γ ∨ γ < q →
      ∃ e : ℝ × ℝ, IsMostInformative (IsBenchEq W q γ) e ∧ e.1 = 1 - e.2) := by sorry

end AnalystRanking.Revelation
