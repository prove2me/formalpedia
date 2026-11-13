-- Prove2me | Theorems.Thm_FairReplay_theorem_10_4
-- name    : FairReplay.theorem_10_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:50:58.776294+00:00
-- url     : https://prove2.me/theorems/89c4449e-12d1-4681-b6b7-f97ea728e96f
-- title:
--   Theorem 10.4 — counterfactual replay changes the small-gap exponent: $Q_{\mathrm{edge}}=\Theta(\log(1/\delta)/d)$, $Q_{\mathrm{vertex}}=\Theta(\log(1/\delta)/d^2)$
-- statement:
--   **Setting.** Fix $p>0$, $s>0$, $d>0$ with $p+s+d<1$, and $\delta\in(0,1/2)$; put $r=1-p-s$. The old thresholds at a fairness edge $(u,v)$ are $(p,p)$; the null new thresholds are $(p+s,p+s)$ and the alternative new thresholds are $(p+s+d,p+s)$. Vertex-paired and four-way rounds reveal their ordered raw outputs, and tapes are independent across rounds.
--
--   1. **(i), test.** Under four-way counterfactual replay there is a test using
--   $$n_{\mathrm{edge}}=\left\lceil\frac{\log\delta}{\log(1-d)}\right\rceil$$
--   rounds with zero type-I error and type-II error at most $\delta$.
--   2. **(i), lower bound.** Every adaptive $\delta$-correct four-way tester with finite expected stopping time satisfies, on the null,
--   $$\mathbb E_0[T]\ge\frac{\mathrm{kl}(1-\delta,\delta)}{r\log\frac{r}{r-d}} .$$
--   3. **(ii), test.** Under vertex-paired replay, even granting the tester $p$, $s$ and the identity of $u$, a $\delta$-correct test exists using
--   $$n_{\mathrm{vertex}}=\left\lceil\frac{2\log(1/\delta)}{d^2}\right\rceil$$
--   raw vertex-pair rounds.
--   4. **(ii), lower bound.** Every adaptive $\delta$-correct vertex-paired tester with finite expected stopping time satisfies
--   $$\mathbb E_0[T]\ge\frac{\mathrm{kl}(1-\delta,\delta)}{s\log\frac{s}{s+d}+r\log\frac{r}{r-d}} .$$
--   5. **Rates (37).** Consequently, for fixed $p,s$ with $r>0$ and fixed $\delta$, as $d\to0$,
--   $$Q_{\mathrm{edge}}(d,\delta)=\Theta\Bigl(\frac{\log(1/\delta)}{d}\Bigr),\qquad Q_{\mathrm{vertex}}(d,\delta)=\Theta\Bigl(\frac{\log(1/\delta)}{d^2}\Bigr):$$
--   there are $c,C,d_0>0$, chosen before $d$, with $c\log(1/\delta)/d\le Q_{\mathrm{edge}}(d,\delta)\le C\log(1/\delta)/d$ and $c\log(1/\delta)/d^2\le Q_{\mathrm{vertex}}(d,\delta)\le C\log(1/\delta)/d^2$ for all $d\in(0,d_0)$.
--
--   Synchronizing both versions at both endpoints on one tape therefore changes the dependence of the testing cost on a small fairness regression $d$ from $d^{-2}$ to $d^{-1}$.
--
--   **Formalization Note** $Q_{\mathrm{edge}}$ and $Q_{\mathrm{vertex}}$ are the infima of $\mathbb E_0[\tau]$ over $\delta$-correct testers, in $[0,\infty]$; $\mathrm{kl}$ is `BanditAlgorithm.bernoulliRelativeEntropy`. The condition $d_0\le r$ keeps every $d\in(0,d_0)$ inside the theorem's domain.
--
--   Differences from the source:
--   - reading: an adaptive tester: actions, stopping time T and accept/reject decision depending on the past transcript → a triple (π, τ, ψ) on the platform's sequential-sampling model: a BanditPolicy over the replay actions, an IsBanditStoppingTime τ (value ⊤ = never stops) and a decision ψ measurable for the stopped σ-algebra; each round's raw ordered outputs are passed as the real number obsCode(outputs); reason: obsCode is injective, so the tester sees the raw ordered transcript; the class is the paper's own 'sequential tester adapted to the independent-round transcript filtration' (Prop. 10.10(i), p.23); randomness outside the transcript (a private seed for τ or ψ) is not modelled, so in the one-action four-way model τ and ψ are functions of the transcript alone
--   - reading: δ-correct: both errors at most δ, for a tester 'terminating with a decision' (Prop. 10.10(i)) → IsDeltaCorrect: P₀(τ < ∞ ∧ reject) ≤ δ and P₁(¬(τ < ∞ ∧ reject)) ≤ δ, so non-stopping counts as a type-II error; reason: every tester that terminates with both errors ≤ δ satisfies it, so the lower bounds cover at least the paper's class; it keeps the never-stopping tester out of the upper bounds and of Q
--   - reading: a test using n_edge (resp. n_vertex) rounds → τ ω = n_edge (resp. n_vertex) for every trajectory ω (a fixed sample size); reason: the stronger of the two readings (rather than τ ≤ n); the paper's tests run exactly n rounds (proof, p.15)
--   - reading: Q_edge(d, δ), Q_vertex(d, δ) (not defined in the paper) → optRounds: the infimum of E₀[τ] over δ-correct testers of the access model, in ℝ≥0∞; reason: the paper's own usage: 'the optimal expected null declared cost' (Thm 10.9(vi), p.20), 'the minimax null-expected round complexity' (Prop. 10.10, p.23)
--   - reading: Θ(·) as d → 0 with δ fixed, for fixed p, s, r > 0, up to constant factors → ∀ p s δ, ∃ c C d₀ > 0 with d₀ ≤ 1 − p − s, ∀ d ∈ (0, d₀), two-sided bounds for both Q's; reason: constants chosen before d and after (p, s, δ), as 'with δ fixed' says; they cannot be uniform in δ, since kl(1 − δ, δ) → 0 as δ → 1/2
--   - reading: 'Counting concrete program executions multiplies the two costs by four and two, respectively, and therefore does not change the exponent separation.' → not stated; reason: a change of cost unit: execution counts are 4× and 2× the round counts, so the Θ statements are unchanged
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.4, eqs. (33)–(37), p.14 (PDF p.16)

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_FairReplay_fourWayModel
import Definitions.Def_FairReplay_vertexModel
import Definitions.Def_FairReplay_IsDeltaCorrect
import Definitions.Def_FairReplay_expectedRounds
import Definitions.Def_FairReplay_optRounds

open MeasureTheory

namespace FairReplay

/-- **Theorem 10.4 (Counterfactual replay changes the small-gap exponent)** (Sah, Zhang, Lian,
*Testing Fairness of Evolving Software under Uncertainty*, STOC 2027 submission (manuscript of
2026-11-03, sha256 e23940a0…), Theorem 10.4, eqs. (33)–(37), p.14 (PDF p.16)).

Fix `p, s, d > 0` with `p + s + d < 1` and `δ ∈ (0, 1/2)`, and put `r = 1 − p − s`. Old thresholds
`(p, p)`; null new thresholds `(p + s, p + s)`; alternative new thresholds `(p + s + d, p + s)`.

1. (i), test (33): on four-way replay there is a tester with `τ ≡ ⌈log δ / log(1 − d)⌉`, zero
   type-I error and type-II error at most `δ`.
2. (i), lower bound (34): every δ-correct four-way tester with `E₀[τ] < ∞` has
   `E₀[τ] ≥ kl(1 − δ, δ) / (r log(r/(r − d)))`.
3. (ii), test (35): on vertex-paired replay there is a δ-correct tester with
   `τ ≡ ⌈2 log(1/δ)/d²⌉`.
4. (ii), lower bound (36): every δ-correct vertex-paired tester with `E₀[τ] < ∞` has
   `E₀[τ] ≥ kl(1 − δ, δ) / (s log(s/(s + d)) + r log(r/(r − d)))`.
5. (37): for fixed `p, s` (with `r > 0`) and fixed `δ`, there are `c, C, d₀ > 0`, chosen before `d`,
   such that for all `d ∈ (0, d₀)`:
   `c log(1/δ)/d ≤ Q_edge(d, δ) ≤ C log(1/δ)/d` and `c log(1/δ)/d² ≤ Q_vertex(d, δ) ≤ C log(1/δ)/d²`.

**Formalization Note** Testers are triples `(π, τ, ψ)` on the platform's sequential-sampling model:
an adaptive, possibly randomized policy over the replay actions (one action for four-way replay;
`u` = action `0` and `v` = action `1` for vertex-paired replay), a stopping time of the transcript
filtration (`⊤` = never stops), and a decision measurable for the stopped σ-algebra (`true` =
reject). Type II counts non-stopping as an error. "A test using n rounds" means `τ ≡ n`.
`Q_edge`, `Q_vertex` are the infima of `E₀[τ]` over δ-correct testers, in `ℝ≥0∞`. `d₀ ≤ r` keeps
every `d ∈ (0, d₀)` inside the theorem's domain `p + s + d < 1`. `kl` is
`BanditAlgorithm.bernoulliRelativeEntropy`. The remark on counting concrete program executions
(a factor four and two) is about cost units and is not part of the statement. -/
theorem theorem_10_4 :
    (∀ p s d δ : ℝ, 0 < p → 0 < s → 0 < d → p + s + d < 1 → 0 < δ → δ < 1 / 2 →
      -- (i), the four-way test (33)
      (∃ (π : BanditAlgorithm.BanditPolicy 1) (τ : (ℕ → Fin 1 × ℝ) → ℕ∞)
          (ψ : (ℕ → Fin 1 × ℝ) → Bool) (hτ : BanditAlgorithm.IsBanditStoppingTime τ),
          Measurable[hτ.measurableSpace] ψ ∧
          (∀ ω, τ ω = ((⌈Real.log δ / Real.log (1 - d)⌉₊ : ℕ) : ℕ∞)) ∧
          BanditAlgorithm.banditTrajMeasure (fourWayModel p s d false) π
              {ω | τ ω < ⊤ ∧ ψ ω = true} = 0 ∧
          BanditAlgorithm.banditTrajMeasure (fourWayModel p s d true) π
              {ω | ¬ (τ ω < ⊤ ∧ ψ ω = true)} ≤ ENNReal.ofReal δ) ∧
      -- (i), the four-way lower bound (34)
      (∀ (π : BanditAlgorithm.BanditPolicy 1) (τ : (ℕ → Fin 1 × ℝ) → ℕ∞)
          (ψ : (ℕ → Fin 1 × ℝ) → Bool) (hτ : BanditAlgorithm.IsBanditStoppingTime τ),
          Measurable[hτ.measurableSpace] ψ →
          IsDeltaCorrect δ (fourWayModel p s d false) (fourWayModel p s d true) π τ ψ →
          expectedRounds (fourWayModel p s d false) π τ < ⊤ →
          ENNReal.ofReal (BanditAlgorithm.bernoulliRelativeEntropy (1 - δ) δ /
              ((1 - p - s) * Real.log ((1 - p - s) / ((1 - p - s) - d)))) ≤
            expectedRounds (fourWayModel p s d false) π τ) ∧
      -- (ii), the vertex-paired test (35)
      (∃ (π : BanditAlgorithm.BanditPolicy 2) (τ : (ℕ → Fin 2 × ℝ) → ℕ∞)
          (ψ : (ℕ → Fin 2 × ℝ) → Bool) (hτ : BanditAlgorithm.IsBanditStoppingTime τ),
          Measurable[hτ.measurableSpace] ψ ∧
          (∀ ω, τ ω = ((⌈2 * Real.log (1 / δ) / d ^ 2⌉₊ : ℕ) : ℕ∞)) ∧
          IsDeltaCorrect δ (vertexModel p s d false) (vertexModel p s d true) π τ ψ) ∧
      -- (ii), the vertex-paired lower bound (36)
      (∀ (π : BanditAlgorithm.BanditPolicy 2) (τ : (ℕ → Fin 2 × ℝ) → ℕ∞)
          (ψ : (ℕ → Fin 2 × ℝ) → Bool) (hτ : BanditAlgorithm.IsBanditStoppingTime τ),
          Measurable[hτ.measurableSpace] ψ →
          IsDeltaCorrect δ (vertexModel p s d false) (vertexModel p s d true) π τ ψ →
          expectedRounds (vertexModel p s d false) π τ < ⊤ →
          ENNReal.ofReal (BanditAlgorithm.bernoulliRelativeEntropy (1 - δ) δ /
              (s * Real.log (s / (s + d)) +
                (1 - p - s) * Real.log ((1 - p - s) / ((1 - p - s) - d)))) ≤
            expectedRounds (vertexModel p s d false) π τ)) ∧
    -- (37), the Θ rates as d → 0 with p, s, δ fixed
    (∀ p s δ : ℝ, 0 < p → 0 < s → p + s < 1 → 0 < δ → δ < 1 / 2 →
      ∃ c C d₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < d₀ ∧ d₀ ≤ 1 - p - s ∧
        ∀ d : ℝ, 0 < d → d < d₀ →
          ENNReal.ofReal (c * Real.log (1 / δ) / d) ≤ Qedge p s d δ ∧
          Qedge p s d δ ≤ ENNReal.ofReal (C * Real.log (1 / δ) / d) ∧
          ENNReal.ofReal (c * Real.log (1 / δ) / d ^ 2) ≤ Qvertex p s d δ ∧
          Qvertex p s d δ ≤ ENNReal.ofReal (C * Real.log (1 / δ) / d ^ 2)) := by sorry

end FairReplay
