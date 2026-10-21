-- Prove2me | Theorems.Thm_AnalystRank_Informativeness_lemma_1
-- name    : AnalystRank.Informativeness.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:18.387735+00:00
-- url     : https://prove2.me/theorems/7212d094-cca9-4a24-8b3e-7cabb55ef3a7
-- title:
--   Lemma 1 (corrected) — benchmark: the most informative equilibrium exists; it is separating on [1 − γ, γ] and pooling elsewhere
-- statement:
--   Consider the benchmark game, in which each analyst is paid $1$ for a correct forecast and $0$ otherwise, whatever the other analyst does. Let $q\in(0,1)$, $\gamma\in(\tfrac12,1)$ and $\rho\in[0,1]$. Then the benchmark game has a most informative symmetric equilibrium $\sigma_B=(\sigma_B^h,\sigma_B^l)$, and
--
--   $$\sigma_B=(1,1)\ \text{ if } q\in[1-\gamma,\gamma],\qquad \sigma_B^h=1-\sigma_B^l\ \text{ if } q\notin[1-\gamma,\gamma].$$
--
--   Without competition, analysts reveal their signals fully exactly when the prior uncertainty is high, and otherwise their forecasts carry no information. This is the comparison point $\Pi_B$ of Proposition 5.
--
--   **Formalization Note** *Corrected:* the printed Lemma 1 (i) gives the interval $[\gamma,1-\gamma]$, which is empty for $\gamma>\tfrac12$. The derivation on p. 10, the proof of Proposition 1 and Lemma 3 (A) all use $[1-\gamma,\gamma]$, which is stated here. The statement also asserts that the most informative equilibrium exists for every $q\in(0,1)$, which Lemma 1 presupposes.
-- source:
--   Banerjee, Does Competition Improve Analysts’ Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (13 Nov 2017), p. 11, Lemma 1 (interval corrected from [γ, 1 − γ] to [1 − γ, γ], cf. p. 10)

import Mathlib
import Definitions.Def_AnalystRank_Informativeness_Model

namespace AnalystRank.Informativeness

open Set

theorem lemma_1 (q γ ρ : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hγ0 : 1 / 2 < γ) (hγ1 : γ < 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (∃ σB : ℝ × ℝ, IsMostInformative (benchEqSet q γ ρ) σB) ∧
    ∀ σB : ℝ × ℝ, IsMostInformative (benchEqSet q γ ρ) σB →
      (q ∈ Icc (1 - γ) γ → σB = (1, 1)) ∧
      (q ∉ Icc (1 - γ) γ → σB.1 = 1 - σB.2) := by sorry

end AnalystRank.Informativeness
