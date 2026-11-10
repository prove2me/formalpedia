-- Prove2me | Theorems.Thm_BayesOptStop_Scheme_lemma_6
-- name    : BayesOptStop.Scheme.lemma_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:19:41.193218+00:00
-- url     : https://prove2.me/theorems/51ef6063-e95f-44ae-aecc-b80d43af5878
-- title:
--   Lemma 6 — $J=O(\log^*(1/\alpha_0)+1/\varepsilon)$ iterations suffice
-- statement:
--   Suppose $0<\varepsilon\le1$, $0<\alpha_0\le1$ and $\alpha_{j+1}=1/(1+\ln(1/\alpha_j))$ for every $j\ge0$. There is an integer $J=O(\log^*\frac1{\alpha_0}+\frac1\varepsilon)$ with $\alpha_J\ge1-\varepsilon/2$: there is a universal $C>0$ such that for all such $\varepsilon,\alpha_0$ some $J\le C(\log^*(1/\alpha_0)+1/\varepsilon)$ has $\alpha_J\ge1-\varepsilon/2$.
--
--   Differences from the source:
--   - encoding: J = O(log*(1/α₀) + 1/ε) → ∃ C > 0 universal (before ε and α₀) with J ≤ C (log*(1/α₀) + 1/ε); reason: explicit constant
--   - encoding: log* (base unspecified in the statement) → logStarReal, base 2, at a real argument; reason: App. B.6 uses log₂; the base changes log* by an additive constant only
-- source:
--   AmaniHamedani, Aouad, Işık, Kesselheim, Saberi (2026), Bayesian Optimal Stopping: Invincible Prophets and Achievable Philosophers, held STOC 2027 submission, SHA-256 fecfa05a3285ac21a7efbed099d2afed88a382dfcc9d91836b6e5210d70c4241, Lemma 6, p. 20 (proof App. B.6, pp. 45–46)

import Mathlib
import Definitions.Def_BayesOptStop_Scheme_Improvement

namespace BayesOptStop.Scheme

/-- **Lemma 6** (AmaniHamedani, Aouad, Işık, Kesselheim, Saberi 2026, held STOC 2027 submission,
SHA-256 fecfa05a…c4241, p. 20): suppose `0 < ε ≤ 1`, `0 < α₀ ≤ 1` and
`α_{j+1} = 1/(1 + ln(1/α_j))`. There is an integer `J = O(log*(1/α₀) + 1/ε)` with
`α_J ≥ 1 - ε/2`. The `O(·)` constant `C` is universal, chosen before `ε` and `α₀`. -/
theorem lemma_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ ε α₀ : ℝ, 0 < ε → ε ≤ 1 → 0 < α₀ → α₀ ≤ 1 →
      ∃ J : ℕ, (J : ℝ) ≤ C * ((logStarReal (1 / α₀) : ℝ) + 1 / ε) ∧
        1 - ε / 2 ≤ alphaSeq α₀ J := by sorry

end BayesOptStop.Scheme
