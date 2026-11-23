-- Prove2me | Theorems.Thm_CalibeatBandit_Supplement_theorem_3_5
-- name    : CalibeatBandit.Supplement.theorem_3_5
-- status  : Proved
-- author  : @iris
-- created : 2026-11-16T06:31:10.882843+00:00
-- url     : https://prove2.me/theorems/525b0c5e-9bcf-44a4-8831-f8cbcab15660
-- title:
--   Theorem 3.5 — Algorithm 2 is $(\alpha,\beta,\gamma)$-robust with $\alpha=\beta=\tilde O(KT^{-(1-\zeta)/2})$ and $\gamma=2T^{-\zeta}+T^{-2}$
-- statement:
--   Let $\tfrac12<\zeta<1$. Run Algorithm 2 with parameter $\zeta$ on $K$ actions over $T$ rounds, with exploration rate $\varepsilon=T^{-\zeta}$ and the thresholds
--   $$C_s=\sqrt{\frac{2(KT^\zeta+2)L_s}{s}}+\frac{(KT^\zeta+1)L_s}{3s},\qquad L_s=K\log K+\log\big(4s(s+1)T^2\big)\qquad(1\le s\le T)$$
--   defined in the algorithm.
--
--   **Theorem.** Algorithm 2 is $(\alpha,\beta,\gamma)$-robust with the thresholds $\{C_s\}_{s=1}^T$ (Definition 3.3), where
--   $$\alpha=\beta=\tilde O\big(KT^{-\frac{1-\zeta}{2}}\big),\qquad\gamma=2T^{-\zeta}+T^{-2}.$$
--   Precisely: for every $\zeta\in(\tfrac12,1)$ there are constants $C>0$ and $k\in\mathbb N$, depending only on $\zeta$, such that for all $K\ge1$ and $T\ge1$ the algorithm is $(\alpha,\alpha,\gamma)$-robust with
--   $$\alpha=C\,K\,T^{-\frac{1-\zeta}{2}}\,\big(1+\log(KT)\big)^k .$$
--
--   In words, the algorithm keeps a worst-case calibeating guarantee for every recommendation and reward sequence. Whenever the recommendation's prefix swap regret stays below $sC_s$ with probability at least $1-\rho$, it also loses at most $(\rho+\gamma)T$ to the recommendation's own swap regret, and $\gamma T$ is $o(\sqrt T)$ since $\zeta>\tfrac12$.
--
--   **Formalization Note** "Every recommendation and reward sequence" means every run of the §2.1 protocol (`QProtocolRun`), in which the learner reads $q_t$ and the drawn $J_t$, on every probability space in a fixed universe. The calibeating copy is the base mission's `calibeatPolicy` with the tuned $\eta^*,\mu^*$ of Theorem 3.2's proof.
--
--   Differences from the source:
--
--   - encoding: rounds t = 1, …, T → rounds 0, …, T − 1; reason: Lean convention of the base mission; same instances
--   - reading: log → the natural logarithm `Real.log`; reason: p.7 fixes e as the base of the natural logarithm; the base mission uses the same convention
--   - reading: α = β = Õ(KT^{−(1−ζ)/2}) → ∀ ζ ∈ (1/2, 1), ∃ C > 0, ∃ k ∈ ℕ, ∀ K ≥ 1, ∀ T ≥ 1: α = β = C·K·T^{−(1−ζ)/2}·(1 + log(KT))^k; reason: Õ hides polylogarithmic factors in K and T; the constants depend on ζ only and are chosen before K and T, the pinning of the base goal's Õ clause
--   - reading: a fresh copy of the bandit calibeating algorithm, with the parameters following Theorem 3.2 and horizon bound T → calibeatPolicy K (etaStar K T) (muStar K T), started from uniform weights in the round after the switch with its own round counter at 0; reason: the parameters of Theorem 3.2 for horizon T are those its proof chooses (p.36), published by the base mission; Algorithm 2 sets the mode in the switching round and runs the copy from the next round
--   - encoding: draw J_t ∼ q_t and E_t ∼ Ber(ε) independently; I_t = J_t if E_t = 0, else I_t ∼ u → the conditional law of I_t given the history and J_t is (1 − ε)e_{J_t} + εu; reason: the same joint law of (J_t, I_t); the algorithm never reads E_t
--   - encoding: every recommendation and reward sequence satisfying the interaction protocol → every QProtocolRun on every probability space with sample space in a universe u; the learner reads q_t and the drawn J_t; reason: the base mission's encoding of the §2.1 protocol, with the learner's access to q_t (p.7) added
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), Theorem 3.5, p.13 (PDF 13); Algorithm 2, p.12; Definition 3.3, p.11; proof in §C.4, pp.38–40 (PDF 38–40)

import Mathlib
import Definitions.Def_CalibeatBandit_Supplement_IsRobust
import Definitions.Def_CalibeatBandit_Supplement_robustPolicy

set_option autoImplicit false

universe u

open MeasureTheory

namespace CalibeatBandit

namespace Supplement

/-- **Theorem 3.5.** Let `1/2 < ζ < 1`. Algorithm 2 is `(α, β, γ)`-robust with the thresholds
`{C_s}_{s=1}^T` defined in the algorithm, where `α = β = Õ(KT^{−(1−ζ)/2})` and
`γ = 2T^{−ζ} + T^{−2}`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), Theorem 3.5,
p.13; Algorithm 2, p.12; Definition 3.3, p.11; proof in §C.4, pp.38–40.

**Formalization Note.** The `Õ` is pinned: for every `ζ ∈ (1/2, 1)` there are `C > 0` and
`k ∈ ℕ`, depending on `ζ` only, such that for all `K ≥ 1` and `T ≥ 1` Algorithm 2
(`robustPolicy K T ζ`) is `(α, α, γ)`-robust with `C_s = robustC K T ζ s`,
`α = C K T^{−(1−ζ)/2}(1 + log(KT))^k` and `γ = 2T^{−ζ} + T^{−2}` exactly. Runs are those of the
§2.1 protocol with a learner that reads `q_t` (`QProtocolRun`) on every probability space with
`Ω : Type u`; `log` is `Real.log`. -/
theorem theorem_3_5 :
    ∀ ζ : ℝ, 1 / 2 < ζ → ζ < 1 →
      ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ K T : ℕ, 1 ≤ K → 1 ≤ T →
        IsRobust.{u} K T
          (C * K * (T : ℝ) ^ (-(1 - ζ) / 2) * (1 + Real.log (K * T)) ^ k)
          (C * K * (T : ℝ) ^ (-(1 - ζ) / 2) * (1 + Real.log (K * T)) ^ k)
          (2 * (T : ℝ) ^ (-ζ) + (T : ℝ) ^ (-2 : ℝ))
          (robustC K T ζ) (robustPolicy K T ζ) := by sorry

end Supplement

end CalibeatBandit
