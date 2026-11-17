-- Prove2me | Theorems.Thm_FairReplay_Supplement_theorem_10_3_i
-- name    : FairReplay.Supplement.theorem_10_3_i
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:52:21.288456+00:00
-- url     : https://prove2.me/theorems/4fa1b684-85bb-4d25-8733-5da0a046bb0b
-- title:
--   Theorem 10.3(i) — raw-pair replay: $\lceil\log\delta/\log(1-d)\rceil$ rounds suffice, $\mathbb E_0[T]\ge\mathrm{kl}(1-\delta,\delta)/((1-p)\log\frac{1-p}{1-p-d})$
-- statement:
--   In the one-edge family (old thresholds $p$ at both endpoints; null new thresholds $(p,p)$; alternative $(p+d,p)$), fix $p\in(0,1)$, $d\in(0,1-p)$ and $\delta\in(0,1/2)$. Under common-uniform raw-pair replay, where a round at $x\in\{u,v\}$ reveals $(P_0(x;U),P_1(x;U))$ on one uniform tape:
--
--   1. there is a test using
--   $$n_{\mathrm{pair}}=\Big\lceil\frac{\log\delta}{\log(1-d)}\Big\rceil$$
--   paired rounds with zero type-I error and type-II error at most $\delta$;
--   2. every adaptive $\delta$-correct paired-replay tester with finite null expected stopping time satisfies
--   $$\mathbb E_0[T]\ \ge\ \frac{\mathrm{kl}(1-\delta,\delta)}{(1-p)\log\frac{1-p}{1-p-d}}.$$
--
--   Since $(1-p)\log\frac{1-p}{1-p-d}=d+O(d^2)$, shared randomness yields a $d^{-1}$ information channel.
--
--   Differences from the source:
--   - encoding: common-uniform raw-pair replay of the one-edge family → the published vertexModel p 0 d (common shift s = 0): action 0 = round at u, action 1 = round at v; reason: the same two observation laws per hypothesis
--   - encoding: a test using n rounds → a tester whose stopping time is identically n; reason: fixed sample size, the reading of the published base mission (the paper's tests run exactly n rounds)
--   - encoding: an adaptive (δ-correct) tester → a triple (π, T, ψ) on the published sequential-sampling model: possibly randomized adaptive policy, stopping time of the transcript filtration (⊤ = never stops), decision measurable for the stopped σ-algebra; type II counts non-stopping as an error; reason: the tester model of the published base mission; randomized policies contain the deterministic ones, so the class is at least the paper's
--   - encoding: the round reveals its ordered raw Boolean outputs → the output vector is passed to the model through the injective real code obsCode; laws are images of the uniform tape on [0, 1]; reason: an injective code loses no information, so the tester sees the whole transcript
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), §10.2 and Theorem 10.3(i), eqs. (21)–(22), pp.12–13 (PDF pp.14–15)

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_FairReplay_vertexModel
import Definitions.Def_FairReplay_IsDeltaCorrect
import Definitions.Def_FairReplay_expectedRounds

open MeasureTheory

namespace FairReplay.Supplement

/-- **Theorem 10.3(i), raw-pair replay, eqs. (21)–(22)** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0…), §10.2 and Theorem 10.3(i), pp.12–13
(PDF pp.14–15)): "For the one-edge family, the old thresholds are p at both endpoints. The null applies
no differential patch and the alternative adds d to the first endpoint [...] Fix p ∈ (0, 1),
d ∈ (0, 1 − p), and δ ∈ (0, 1/2). [...] (i) Under common-uniform raw-pair replay, there is a test using
npair = ⌈log δ / log(1 − d)⌉ (21) paired rounds with zero type-I error and type-II error at most δ.
Moreover, every adaptive δ-correct paired-replay tester with finite expected stopping time satisfies,
on the null, E0[T] ≥ kl(1 − δ, δ) / ((1 − p) log((1−p)/(1−p−d))). (22)"

For `p ∈ (0, 1)`, `d ∈ (0, 1 − p)` and `δ ∈ (0, 1/2)`:
1. there is a raw-pair tester with `T ≡ ⌈log δ / log(1 − d)⌉`, which never rejects under the null and
   fails to reject with probability at most `δ` under the alternative;
2. every δ-correct raw-pair tester with `E₀[T] < ∞` has
   `E₀[T] ≥ kl(1 − δ, δ) / ((1 − p) log((1 − p)/(1 − p − d)))`.

**Formalization Note** Common-uniform raw-pair replay of the one-edge family is the published
`vertexModel p 0 d`: a round at `u` (action `0`) or `v` (action `1`) observes the coded pair
`(P0(x;U), P1(x;U))`, old thresholds `(p, p)`, new `(p, p)` under the null and `(p + d, p)` under the
alternative (no common shift, `s = 0`). The tester chooses the vertex adaptively. "A test using n
rounds" means `T ≡ n`; type II counts non-stopping as an error. -/
theorem theorem_10_3_i (p d δ : ℝ) (hp : 0 < p) (hp1 : p < 1) (hd : 0 < d) (hdp : d < 1 - p)
    (hδ : 0 < δ) (hδ2 : δ < 1 / 2) :
    (∃ (π : BanditAlgorithm.BanditPolicy 2) (T : (ℕ → Fin 2 × ℝ) → ℕ∞)
        (ψ : (ℕ → Fin 2 × ℝ) → Bool) (hT : BanditAlgorithm.IsBanditStoppingTime T),
        Measurable[hT.measurableSpace] ψ ∧
        (∀ ω, T ω = ((⌈Real.log δ / Real.log (1 - d)⌉₊ : ℕ) : ℕ∞)) ∧
        BanditAlgorithm.banditTrajMeasure (vertexModel p 0 d false) π
            {ω | T ω < ⊤ ∧ ψ ω = true} = 0 ∧
        BanditAlgorithm.banditTrajMeasure (vertexModel p 0 d true) π
            {ω | ¬ (T ω < ⊤ ∧ ψ ω = true)} ≤ ENNReal.ofReal δ) ∧
    (∀ (π : BanditAlgorithm.BanditPolicy 2) (T : (ℕ → Fin 2 × ℝ) → ℕ∞)
        (ψ : (ℕ → Fin 2 × ℝ) → Bool) (hT : BanditAlgorithm.IsBanditStoppingTime T),
        Measurable[hT.measurableSpace] ψ →
        IsDeltaCorrect δ (vertexModel p 0 d false) (vertexModel p 0 d true) π T ψ →
        expectedRounds (vertexModel p 0 d false) π T < ⊤ →
        ENNReal.ofReal (BanditAlgorithm.bernoulliRelativeEntropy (1 - δ) δ /
            ((1 - p) * Real.log ((1 - p) / (1 - p - d)))) ≤
          expectedRounds (vertexModel p 0 d false) π T) := by sorry

end FairReplay.Supplement
