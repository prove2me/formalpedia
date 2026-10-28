-- Prove2me | Theorems.Thm_APrioriTSP_Sampling_lemma_32
-- name    : APrioriTSP.Sampling.lemma_32
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:33.151256+00:00
-- url     : https://prove2.me/theorems/cb05a099-65ae-46ca-93d0-685ac86b64fe
-- title:
--   Lemma 32, p. 31 — for small ε there is a number k of copies matching 1 − (1 − p)^σ and p up to a factor 1 + λ
-- statement:
--   Let $\sigma \in (0,1)$, $\lambda > 0$ and $p \in (0,1]$. Then there is $\varepsilon_p \in (0,1)$ such that for every $\varepsilon \in (0, \varepsilon_p]$ there is $k \in \mathbb N$ with
--
--   1. $1 - (1-\varepsilon)^k \le p \le \varepsilon k$,
--   2. $(1-p)^\sigma \le (1-\sigma\varepsilon)^k$,
--   3. $1 - (1-p)^\sigma \le (1+\lambda)\cdot\big(1 - (1-\sigma\varepsilon)^k\big)$,
--   4. $(1-\varepsilon)^k \le (1+\lambda)\cdot(1-p)$ if $p < 1$, and $(1-\varepsilon)^k \le \lambda$ if $p = 1$.
--
--   In the proof of Lemma 9, each customer $v$ is replaced by $k$ copies of activation probability $\varepsilon$; the lemma controls the probability that some copy is active or sampled.
--
--   **Formalization Note** $(1-p)^\sigma$ is the real power; $(1-\varepsilon)^k$ and $(1-\sigma\varepsilon)^k$ are natural-number powers. The variable $\lambda$ is named `lam` (a Lean keyword otherwise).
--
--   Differences from the source:
--
--   - encoding: k ∈ ℕ → k : ℕ (0 included); reason: the paper's ℕ contains 0 (Lemma 18's base case n = 0); item (i) forces k ≥ 1 anyway, since p > 0
-- source:
--   Blauth, Neuwohner, Puhlmann & Vygen, Improved guarantees for the a priori TSP, arXiv:2309.10663v1, p. 31, Lemma 32

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting

namespace APrioriTSP.Sampling

/-- Lemma 32 (p. 31): choosing the number `k` of copies of a customer. -/
theorem lemma_32 (σ lam p : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hlam : 0 < lam)
    (hp0 : 0 < p) (hp1 : p ≤ 1) :
    ∃ εp : ℝ, 0 < εp ∧ εp < 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ εp → ∃ k : ℕ,
      (1 - (1 - ε) ^ k ≤ p ∧ p ≤ ε * k) ∧
      (1 - p) ^ σ ≤ (1 - σ * ε) ^ k ∧
      1 - (1 - p) ^ σ ≤ (1 + lam) * (1 - (1 - σ * ε) ^ k) ∧
      (p < 1 → (1 - ε) ^ k ≤ (1 + lam) * (1 - p)) ∧
      (p = 1 → (1 - ε) ^ k ≤ lam) := by sorry

end APrioriTSP.Sampling
