-- Prove2me | Theorems.Thm_CalibeatBandit_Supplement_theorem_4_1
-- name    : CalibeatBandit.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:32:19.882177+00:00
-- url     : https://prove2.me/theorems/a2a46cbd-0e89-471e-a037-e0e0df2abc7d
-- title:
--   Theorem 4.1 — bandit swap regret lower bound $\mathbb E[\mathrm{SR}_T]\ge cK^3/(\log K)^6=cK\sqrt T/(\log K)^6$ at $T=K^4$
-- statement:
--   **Theorem.** There exist absolute constants $c>0$ and $K_0$ such that the following holds. Let $K\ge K_0$ be the number of actions and $T=K^4$ the time horizon. Then every $K$-action bandit algorithm has a deterministic oblivious reward sequence $y_1,\dots,y_T\in[0,1]^K$ such that
--   $$\mathbb E[\mathrm{SR}_T]\ge\frac{cK^3}{(\log K)^6}=\frac{cK\sqrt T}{(\log K)^6}.$$
--   Here $\mathrm{SR}_T=\max_{\sigma:[K]\to[K]}\sum_{t=1}^T\big(y_t(\sigma(I_t))-y_t(I_t)\big)$ is the swap regret of the algorithm's actions $I_t$, and the expectation is over the algorithm's randomness.
--
--   This shows that the $\tilde O(K\sqrt T)$ swap regret of the bandit calibeating algorithm (Theorem 3.2) is optimal up to logarithmic factors. It is a new lower bound for swap regret minimization under bandit feedback.
--
--   **Formalization Note** A bandit algorithm is given by its conditional mixed strategies (`BanditAlg K`), which are probability vectors on every input. The reward sequence is chosen after the algorithm and does not react to its actions. $\mathbb E[\mathrm{SR}_T]$ is the explicit expectation `expectedSwapRegret` over the law of the action sequence. Rewards beyond round $T$ are unused but also required to lie in $[0,1]$.
--
--   Differences from the source:
--
--   - encoding: rounds t = 1, …, T → rounds 0, …, T − 1; reason: Lean convention of the base mission; same instances
--   - reading: log → the natural logarithm `Real.log`; reason: p.7 fixes e as the base of the natural logarithm; the base mission uses the same convention
--   - encoding: every K-action bandit algorithm (with private randomness and state) → every family of conditional mixed strategies A_t(I_{<t}; y_{<t}(I_{<t})) that are probability vectors on every input; reason: against a fixed reward sequence every algorithm induces the same action law as its behavioural conditionals, which depend on the rewards only through the observed ones; conditionals on unreachable inputs can be completed arbitrarily
--   - encoding: E[SR_T] → the finite sum over action sequences of the product of conditional probabilities times the swap regret; reason: the law of the actions against a deterministic oblivious sequence; the swap regret is the base definition written over Fin T
--   - encoding: y_1, …, y_T ∈ [0,1]^K → y : ℕ → Fin K → ℝ with y t i ∈ [0,1] for every t and i; reason: entries after round T are never read and can be set to 0
--   - encoding: E[SR_T] ≥ cK³/(log K)⁶ = cK√T/(log K)⁶ → c·K³/(log K)⁶ ≤ E[SR_T]; reason: the two bounds are equal because T = K⁴
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), Theorem 4.1, p.13 (PDF 13); proof in §4, pp.13–21 (PDF 13–21), and App. D

import Mathlib
import Definitions.Def_CalibeatBandit_IsProbVec
import Definitions.Def_CalibeatBandit_Supplement_BanditAlg

set_option autoImplicit false

namespace CalibeatBandit

namespace Supplement

/-- **Theorem 4.1 (bandit swap-regret lower bound).** There exist absolute constants `c > 0` and
`K_0` such that, for every number of actions `K ≥ K_0` and time horizon `T = K⁴`, every
`K`-action bandit algorithm has a deterministic oblivious reward sequence
`y_1, …, y_T ∈ [0, 1]^K` such that `E[SR_T] ≥ cK³/(log K)⁶ = cK√T/(log K)⁶`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), Theorem 4.1,
p.13; proof in §4, pp.13–21, and App. D.

**Formalization Note.** `c` and `K_0` are chosen before `K`. A bandit algorithm is given by its
conditional mixed strategies (`BanditAlg K`, probability vectors on every input); the reward
sequence `y` is chosen after the algorithm and does not depend on its actions (deterministic,
oblivious), with every entry in `[0, 1]`. `E[SR_T]` is the explicit expectation
`expectedSwapRegret` over the law of the action sequence; `T = K⁴` exactly; `log` is
`Real.log`. The identity `cK³/(log K)⁶ = cK√T/(log K)⁶` holds because `T = K⁴`. -/
theorem theorem_4_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
      ∀ A : BanditAlg K, (∀ t a r, IsProbVec (A t a r)) →
        ∃ y : ℕ → Fin K → ℝ, (∀ t i, y t i ∈ Set.Icc (0 : ℝ) 1) ∧
          c * (K : ℝ) ^ 3 / (Real.log K) ^ 6 ≤ expectedSwapRegret A (K ^ 4) y := by sorry

end Supplement

end CalibeatBandit
