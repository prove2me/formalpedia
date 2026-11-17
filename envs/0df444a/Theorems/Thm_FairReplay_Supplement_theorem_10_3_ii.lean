-- Prove2me | Theorems.Thm_FairReplay_Supplement_theorem_10_3_ii
-- name    : FairReplay.Supplement.theorem_10_3_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:53:13.971607+00:00
-- url     : https://prove2.me/theorems/f41d47e6-3c67-4f0c-af25-f6fd7225a7a5
-- title:
--   Theorem 10.3(ii) — independent observation: $\lceil 2\log(1/\delta)/d^2\rceil$ calls suffice, $\mathbb E_0[T]\ge\mathrm{kl}(1-\delta,\delta)/\mathrm{kl}(p,p+d)$
-- statement:
--   In the one-edge family, fix $p\in(0,1)$, $d\in(0,1-p)$ and $\delta\in(0,1/2)$. Under independent observation, each call executes one program version at one endpoint on a fresh tape and observes its output.
--
--   1. When the old baseline $p$ is known, a test using
--   $$n_{\mathrm{ind}}=\Big\lceil\frac{2\log(1/\delta)}{d^2}\Big\rceil$$
--   single-execution new-version calls at $u$ is $\delta$-correct.
--   2. Every adaptive $\delta$-correct independent-replay tester (using any of the four single-execution calls) with finite null expected stopping time satisfies
--   $$\mathbb E_0[T]\ \ge\ \frac{\mathrm{kl}(1-\delta,\delta)}{\mathrm{kl}(p,p+d)}.$$
--
--   Since $\mathrm{kl}(p,p+d)=\frac{d^2}{2p(1-p)}+O(d^3)$, fresh observation only has a $d^{-2}$ channel.
--
--   Differences from the source:
--   - encoding: independent observation (single-version calls, fresh tapes) → indepModel p d: four actions P0(u), P1(u), P0(v), P1(v), each the coded single output on a fresh uniform tape; reason: the four single-execution calls of the one-edge family
--   - encoding: new-version calls at u; baseline p known → the policy plays action 1 in every round; p is a parameter of the statement, so the tester may depend on it; reason: direct transcription
--   - encoding: a test using n rounds → a tester whose stopping time is identically n; reason: fixed sample size, the reading of the published base mission (the paper's tests run exactly n rounds)
--   - encoding: an adaptive (δ-correct) tester → a triple (π, T, ψ) on the published sequential-sampling model: possibly randomized adaptive policy, stopping time of the transcript filtration (⊤ = never stops), decision measurable for the stopped σ-algebra; type II counts non-stopping as an error; reason: the tester model of the published base mission; randomized policies contain the deterministic ones, so the class is at least the paper's
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.3(ii), eqs. (23)–(24), p.13 (PDF p.15)

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_FairReplay_IsDeltaCorrect
import Definitions.Def_FairReplay_expectedRounds
import Definitions.Def_FairReplay_Supplement_indepModel

open MeasureTheory

namespace FairReplay.Supplement

/-- **Theorem 10.3(ii), independent new-version observation, eqs. (23)–(24)** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0…), Theorem
10.3(ii), p.13 (PDF p.15)): "Fix p ∈ (0, 1), d ∈ (0, 1 − p), and δ ∈ (0, 1/2). [...] (ii) Under
independent new-version observation, a test using nind = ⌈2 log(1/δ) / d²⌉ (23) single-execution
new-version calls at u is δ-correct when the retained old baseline p is known. Conversely, every
adaptive δ-correct independent-replay tester with finite expected stopping time satisfies
E0[T] ≥ kl(1 − δ, δ) / kl(p, p + d). (24)"

For `p ∈ (0, 1)`, `d ∈ (0, 1 − p)` and `δ ∈ (0, 1/2)`:
1. there is a δ-correct tester on the independent single-execution model that calls only the new
   version at `u` (action `1`) in every round and stops after exactly `⌈2 log(1/δ)/d²⌉` calls;
2. every δ-correct tester on that model (using any of the four single-execution actions,
   adaptively) with `E₀[T] < ∞` has `E₀[T] ≥ kl(1 − δ, δ) / kl(p, p + d)`.

**Formalization Note** The model `indepModel p d` has the four actions `P0(u), P1(u), P0(v), P1(v)`,
each a single execution on a fresh tape. "Known baseline p": `p` is a parameter of the statement, so
the tester may depend on it. `kl(x, y) = x log(x/y) + (1 − x) log((1 − x)/(1 − y))` is
`BanditAlgorithm.bernoulliRelativeEntropy`. -/
theorem theorem_10_3_ii (p d δ : ℝ) (hp : 0 < p) (hp1 : p < 1) (hd : 0 < d) (hdp : d < 1 - p)
    (hδ : 0 < δ) (hδ2 : δ < 1 / 2) :
    (∃ (π : BanditAlgorithm.BanditPolicy 4) (T : (ℕ → Fin 4 × ℝ) → ℕ∞)
        (ψ : (ℕ → Fin 4 × ℝ) → Bool) (hT : BanditAlgorithm.IsBanditStoppingTime T),
        (∀ t (h : BanditAlgorithm.BanditHistory 4 t), π.select t h = Measure.dirac 1) ∧
        Measurable[hT.measurableSpace] ψ ∧
        (∀ ω, T ω = ((⌈2 * Real.log (1 / δ) / d ^ 2⌉₊ : ℕ) : ℕ∞)) ∧
        IsDeltaCorrect δ (indepModel p d false) (indepModel p d true) π T ψ) ∧
    (∀ (π : BanditAlgorithm.BanditPolicy 4) (T : (ℕ → Fin 4 × ℝ) → ℕ∞)
        (ψ : (ℕ → Fin 4 × ℝ) → Bool) (hT : BanditAlgorithm.IsBanditStoppingTime T),
        Measurable[hT.measurableSpace] ψ →
        IsDeltaCorrect δ (indepModel p d false) (indepModel p d true) π T ψ →
        expectedRounds (indepModel p d false) π T < ⊤ →
        ENNReal.ofReal (BanditAlgorithm.bernoulliRelativeEntropy (1 - δ) δ /
            BanditAlgorithm.bernoulliRelativeEntropy p (p + d)) ≤
          expectedRounds (indepModel p d false) π T) := by sorry

end FairReplay.Supplement
