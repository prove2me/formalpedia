-- Prove2me | Theorems.Thm_BayesOptStop_Scheme_lemma_5
-- name    : BayesOptStop.Scheme.lemma_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:20:39.98503+00:00
-- url     : https://prove2.me/theorems/42724d1d-7351-440a-ac39-54aa4ec756e8
-- title:
--   Lemma 5 — Algorithm 2 with estimated martingales: $r(A_j)\ge\alpha_j(1-\beta)^2\mathbb E[M_j]\ge\alpha_j(1-\beta)^2\mathrm{ON}$
-- statement:
--   Suppose $0<\beta<1$ and $A$ is an $\alpha$-competitive algorithm with $0<\alpha\le1$. If Algorithm 2 starts with the baseline $A$ and $\alpha_0=\alpha$, and uses estimation accuracy $\beta$ when calling Algorithm 1, then every constructed level $j\ge0$ satisfies
--   $$r(A_j)\ge\alpha_j(1-\beta)^2\,\mathbb E[M_j]\ge\alpha_j(1-\beta)^2\,\mathrm{ON}.$$
--   The estimates $L_t$ of $Z^{(\ell)}_t$ at level $\ell$ come from any estimator meeting the accuracy-$\beta$, failure-$\beta/n$ guarantee, with fresh independent seeds at each time.
--
--   Differences from the source:
--   - encoding: A is α-competitive (Algorithm 2's baseline) → A is a valid online policy (measurable in its randomness, stopping at time s depends on h_{s+1}) with r(A) ≥ α E[Z^(0)_1], Z^(0) the Doob martingale of M_0 = max_t X_t; reason: Algorithm 2 measures its baseline against M_0 (base case j = 0 of the proof); measurability makes r(A) an integral
--   - reading: uses estimation accuracy β when calling Algorithm 1 → for every level ℓ the estimator of Z^(ℓ) is measurable in its seed, depends only on h_t, and at every reachable h_t gives L_t/Z^(ℓ)_t ∈ [1 − β, 1] with probability ≥ 1 − β/n; seeds are fresh and independent across times and of the path; reason: Algorithm 1 line 8 with ε = β and Step 3 of the proof (Lemma 4 with failure β/n, U independent of the path)
--   - encoding: draw Q ∈ [α, 1] with density 1/(q ln(1/α)); with probability γ run A → Q = α^V with V ~ Uniform(0,1); A runs iff a uniform c < γ; at α = 1, Q = 1 and the threshold branch has probability 0; reason: the same law for α < 1; the density is undefined at α = 1
--   - encoding: r(A) is the expected reward over H, X and the algorithm's randomness; never selecting earns 0 → `reward`: integral over the policy's seed law of the mixture expectation of the payoff, payoff 0 at times ≥ n; reason: the paper's convention X_τ = 0 on {τ = ∞}
--   - encoding: histories h_t are sequences of observed values; times t ∈ [n] are 1-based → paths ω : Fin n → Fin m of value indices, histories are value cylinders `Agree t` (first t values equal), times 0-based (the paper's X_t is X ⟨t-1⟩, Z_t at history length t); reason: Lean convention; conditioning is on values, so repeated v_q give the paper's filtration
--   - encoding: conditional expectations and ratios X_t/Z_t at a zero-probability history or with Z_t = 0 are not defined → 0/0 = 0 and x/0 = 0 (Lean's division); reason: these cases are excluded by the source or have probability 0; the convention changes no statement about reachable histories
--   - generalization: the horizon has at least one observation → n = 0 is also admitted; reason: at horizon zero every reward, M_j expectation and ON is zero, so both inequalities are 0 ≤ 0
-- source:
--   AmaniHamedani, Aouad, Işık, Kesselheim, Saberi (2026), Bayesian Optimal Stopping: Invincible Prophets and Achievable Philosophers, held STOC 2027 submission, SHA-256 fecfa05a3285ac21a7efbed099d2afed88a382dfcc9d91836b6e5210d70c4241, Lemma 5, p. 20 (proof §3.4.2, pp. 21–23)

import Mathlib
import Definitions.Def_BayesOptStop_Scheme_Algorithms

namespace BayesOptStop.Scheme

/-- **Lemma 5** (AmaniHamedani, Aouad, Işık, Kesselheim, Saberi 2026, held STOC 2027 submission,
SHA-256 fecfa05a…c4241, p. 20): suppose `0 < β < 1` and `A` is `α`-competitive with `0 < α ≤ 1`.
If Algorithm 2 starts with the baseline `A` and `α₀ = α`, and uses estimation accuracy `β` when
calling Algorithm 1, then every constructed level `j ≥ 0` satisfies
`r(A_j) ≥ α_j (1-β)² E[M_j] ≥ α_j (1-β)² ON`.
The level-`ℓ` estimates of `Z^(ℓ)` come from any estimator meeting the accuracy-`β`,
failure-`β/n` guarantee, with fresh independent seeds (Algorithm 1 line 8; Step 3, p. 22). -/
theorem lemma_5 {K m n : ℕ} (I : Instance K m n) (hI : I.Valid) (hS : I.Standing)
    (β α : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (A : Policy m n) (hA : I.PolicyValid A) (hcomp : I.Competitive A α I.pathMax)
    (E : ℕ → Estimator m n) (hE : ∀ ℓ, I.EstimatorGuarantee (E ℓ) (I.Zseq α ℓ) β) (j : ℕ) :
    alphaSeq α j * (1 - β) ^ 2 * I.expect (I.Mseq α j) ≤ I.reward (I.alg2 A α E j) ∧
      alphaSeq α j * (1 - β) ^ 2 * I.ON ≤ alphaSeq α j * (1 - β) ^ 2 * I.expect (I.Mseq α j) := by sorry

end BayesOptStop.Scheme
