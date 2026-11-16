-- Prove2me | Theorems.Thm_CtxSearchTSR_Supplement_theorem_3_4_adversarial_bilateral_trade
-- name    : CtxSearchTSR.Supplement.theorem_3_4_adversarial_bilateral_trade
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:24:27.010514+00:00
-- url     : https://prove2.me/theorems/e2c60c0e-be2f-4105-8a10-6452de77742a
-- title:
--   Theorem 3.4 — adversarial bilateral trade: $\sum_t\mathbb E[\ell_t]\le 2^{12}\sqrt d+1$
-- statement:
--   Fix a seller–buyer pair $w=(s,b)\in K=B_2^d\times B_2^d$, i.e. $\|s\|_2\le1$ and $\|b\|_2\le1$. Let $\mathcal L$ be any lottery rule as in Lemma 3.3: for every state $(m,R)$ with $R=\operatorname{diag}(R_S,R_B)\succ0$, every context $\|x\|_2\le1$ and every slack $\gamma\in(0,1]$, $\mathcal L$ returns a finite lottery of plans with block-diagonal positive-definite successor matrices satisfying (21) for every $w'\in K$. Let the contexts be chosen by any adaptive strategy from the observed history, with $\|x_t\|_2\le1$. Then Algorithm 4 (with $m_1=0$, $R_1=I_{2d}/\sqrt d$ and slacks $\gamma_t=\frac1{t(t+1)}$) satisfies, for every horizon $T$,
--
--   $$\sum_{t=1}^T\mathbb E[\ell_t]\le 2^{12}\sqrt d+1,$$
--
--   where $\ell_t=(x_t^\top(b-s))_+(1-Y_t)$ and the expectation is over the learner's draws from the lotteries.
--
--   This is the worst-case counterpart of Theorem 3.2: no prior is needed, and the total lost gain from trade is $O(\sqrt d)$ uniformly in $T$.
--
--   **Formalization Note** The paper specifies Algorithm 4 through Lemma 3.3 ("choose a lottery of plans as in Lemma 3.3"), so the theorem is stated for every lottery rule with that lemma's property. The expected total loss is computed exactly by backward recursion over the finite lotteries.
--
--   Differences from the source:
--   - reading: Algorithm 4 "chooses a lottery of plans as in Lemma 3.3 with current state (mₜ, Rₜ), context xₜ, and slack γₜ" → every lottery rule (a function of state, context and slack) that returns, for every block-diagonal R ≻ 0, ‖x‖₂ ≤ 1 and γ ∈ (0, 1], a finite lottery of plans with block-diagonal positive-definite successors satisfying (21) for all w ∈ K; reason: the paper defines the algorithm only through the lemma's property ("the lottery can be chosen as a function of the state and context"), and every lottery the lemma supplies is such a rule
--   - reading: "every admissible adaptive context strategy with ‖xₜ‖₂ ≤ 1" → a deterministic map from the observed history (contexts, drawn plans, trade bits) to the next context, which may depend on the fixed w; reason: a strategy with its own randomness independent of the learner's draws is a mixture of deterministic ones, and the bound passes to it by averaging (the base mission's Theorem 2.4 uses the same reading)
--   - generalization: d ≥ 1 implicit → every d ∈ ℕ; reason: at d = 0 every loss is 0 and the bound reads 0 ≤ 1
--   - encoding: Σₜ 𝔼[ℓₜ] → the exact expectation of Σₜ ℓₜ over the T successive draws, by backward recursion; reason: Σ𝔼 = 𝔼Σ, and the lotteries are finite
--   - encoding: m₁ = 0 ∈ ℝ^{2d}, R₁ = I_{2d}/√d, R = diag(R_S, R_B) → the four blocks (m_S, m_B, R_S, R_B) with R_S = R_B = (√d)⁻¹ I_d; reason: same state
--   - encoding: rounds t = 1, …, T with γₜ = 1/(t(t+1)) → rounds 0, …, T − 1 with slack 1/((t+1)(t+2)); reason: Lean indexing; same slacks
-- source:
--   Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, Contextual Search and Bilateral Trade with a Trace-Square-Root Potential, STOC 2027 submission manuscript (sha256 70eeb0d19227c9eee557cdff5598f97062f442373fcde3a3eb76a6cb65a2ad6c), §3.2, Theorem 3.4, p.16, (22); Algorithm 4 p.16; Lemma 3.3 (21) p.15; (20) p.14

import Mathlib
import Definitions.Def_CtxSearchTSR_Supplement_Algorithm4

open Matrix

namespace CtxSearchTSR.Supplement

/-- **Theorem 3.4 (Adversarial Bilateral Trade).** Cosson et al., *Contextual Search and Bilateral
Trade with a Trace-Square-Root Potential*, STOC 2027 submission (manuscript sha256 70eeb0d1…),
p.16, (22).

"For every fixed w ∈ K, every admissible adaptive context strategy with ‖xₜ‖₂ ≤ 1, and every
horizon T, Algorithm 4 satisfies Σ_{t=1}^T E[ℓₜ] ≤ 2¹²√d + 1. (22)"

**Formalization Note.** w = (s, b) with ‖s‖₂ ≤ 1 and ‖b‖₂ ≤ 1 (K = B₂^d × B₂^d). Algorithm 4 draws
from `𝓛 (mₜ, Rₜ) xₜ γₜ`, for any lottery rule `𝓛` with the property Lemma 3.3 provides
(`ValidLotteryRule`), which is how the paper's algorithm is specified ("choose a lottery of plans
as in Lemma 3.3"). The context strategy is any function of the observed history (contexts, drawn
plans, trade bits); it may depend on w and never sees the current draw. The expectation is over
the learner's draws (`alg4ExpectedTotalLoss`). T = 0 is allowed. -/
theorem theorem_3_4_adversarial_bilateral_trade {d : ℕ} (s b : Fin d → ℝ)
    (hs : eucNorm s ≤ 1) (hb : eucNorm b ≤ 1)
    (𝓛 : BState d → (Fin d → ℝ) → ℝ → Lottery d) (h𝓛 : ValidLotteryRule 𝓛)
    (X : AdvTradeStrategy d) (hX : ∀ h, eucNorm (X h) ≤ 1) (T : ℕ) :
    alg4ExpectedTotalLoss 𝓛 X s b T ≤ 2 ^ 12 * Real.sqrt d + 1 := by sorry

end CtxSearchTSR.Supplement
