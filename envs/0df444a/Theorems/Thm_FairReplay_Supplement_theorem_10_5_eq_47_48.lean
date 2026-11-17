-- Prove2me | Theorems.Thm_FairReplay_Supplement_theorem_10_5_eq_47_48
-- name    : FairReplay.Supplement.theorem_10_5_eq_47_48
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:54:18.425136+00:00
-- url     : https://prove2.me/theorems/cd64849d-324f-45eb-936f-c8206e5e6ed6
-- title:
--   Theorem 10.5, eqs. (47)–(48) — boundary KL $K_\tau(d)=\tau\log\frac{\tau}{\tau+d}+r\log\frac{r}{r-d}$ and $\mathbb E_0[T]\ge\mathrm{kl}(1-\delta,\delta)/K_\tau(d)$
-- statement:
--   In the P18 family fix $p>0$, $s\ge0$, $\tau\ge0$, $d>0$ with $p+s+\tau+d<1$, and $\delta\in(0,1/2)$; put $r=1-p-s-\tau$. Old thresholds are $(p,p)$, boundary-null new thresholds $(p+s+\tau,p+s)$ and alternative new thresholds $(p+s+\tau+d,p+s)$; each round reveals the ordered raw four-way transcript.
--
--   1. One four-way round has null-to-alternative KL divergence
--   $$K_\tau(d)=\tau\log\frac{\tau}{\tau+d}+r\log\frac{r}{r-d},$$
--   where the first term is $0$ when $\tau=0$.
--   2. Every adaptive $\delta$-correct tester with finite null expected stopping time satisfies
--   $$\mathbb E_0[T]\ \ge\ \frac{\mathrm{kl}(1-\delta,\delta)}{K_\tau(d)}.$$
--
--   For fixed $\tau>0$, $K_\tau(d)$ is of order $d^2$, so a positive tolerance removes the linear replay channel.
--
--   Differences from the source:
--   - encoding: null-to-alternative KL of one round → Mathlib klDiv of the two round laws, in ℝ≥0∞, equal to ENNReal.ofReal of the closed form; reason: the closed form is a nonnegative real
--   - encoding: the first term is zero when τ = 0 → Lean's 0 · log(0/d) = 0; reason: same value
--   - encoding: an adaptive (δ-correct) tester → a triple (π, T, ψ) on the published sequential-sampling model: possibly randomized adaptive policy, stopping time of the transcript filtration (⊤ = never stops), decision measurable for the stopped σ-algebra; type II counts non-stopping as an error; reason: the tester model of the published base mission; randomized policies contain the deterministic ones, so the class is at least the paper's
--   - encoding: the round reveals its ordered raw Boolean outputs → the output vector is passed to the model through the injective real code obsCode; laws are images of the uniform tape on [0, 1]; reason: an injective code loses no information, so the tester sees the whole transcript
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), §10.3 and Theorem 10.5, eqs. (47)–(48), pp.15–16 (PDF pp.17–18)

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_FairReplay_fourWayModel
import Definitions.Def_FairReplay_IsDeltaCorrect
import Definitions.Def_FairReplay_expectedRounds
import Definitions.Def_FairReplay_Supplement_fourWayEnv

open MeasureTheory InformationTheory

namespace FairReplay.Supplement

/-- **Theorem 10.5, eqs. (47)–(48), the boundary KL and lower bound** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0…), §10.3 and Theorem 10.5,
pp.15–16 (PDF pp.17–18)): "For P18, fix p > 0, s ≥ 0, τ ≥ 0, and d > 0 with p + s + τ + d < 1. The old
thresholds are (p, p); the boundary-null new thresholds are (p + s + τ, p + s) and the alternative
thresholds are (p + s + τ + d, p + s). Each round reveals the ordered raw four-way transcript.
Theorem 10.5 [...] Let δ ∈ (0, 1/2) and set r = 1 − p − s − τ. One four-way synchronized replay round
has null-to-alternative KL Kτ(d) = τ log(τ/(τ + d)) + r log(r/(r − d)), (47) where the first term is
zero when τ = 0. Every adaptive δ-correct tester with finite null expected stopping time satisfies
E0[T] ≥ kl(1 − δ, δ)/Kτ(d). (48)"

With `r = 1 − p − s − τ`:
1. the KL divergence from the law of one four-way round at the boundary null to its law at the
   alternative is `K_τ(d) = τ log(τ/(τ + d)) + r log(r/(r − d))`;
2. every δ-correct four-way tester for the boundary null against the alternative with `E₀[T] < ∞` has
   `E₀[T] ≥ kl(1 − δ, δ)/K_τ(d)`.

**Formalization Note** At `τ = 0` the term `τ log(τ/(τ + d))` is `0 · log 0 = 0` in Lean, which is the
paper's convention. KL is Mathlib's `klDiv` in `ℝ≥0∞`. The stopping time is named `T`. -/
theorem theorem_10_5_eq_47_48 (p s τ d δ : ℝ) (hp : 0 < p) (hs : 0 ≤ s) (hτ : 0 ≤ τ) (hd : 0 < d)
    (hsum : p + s + τ + d < 1) (hδ : 0 < δ) (hδ2 : δ < 1 / 2) :
    klDiv (fourWayLaw ![p, p] ![p + s + τ, p + s]) (fourWayLaw ![p, p] ![p + s + τ + d, p + s]) =
        ENNReal.ofReal (τ * Real.log (τ / (τ + d)) +
          (1 - p - s - τ) * Real.log ((1 - p - s - τ) / ((1 - p - s - τ) - d))) ∧
      ∀ (π : BanditAlgorithm.BanditPolicy 1) (T : (ℕ → Fin 1 × ℝ) → ℕ∞)
        (ψ : (ℕ → Fin 1 × ℝ) → Bool) (hT : BanditAlgorithm.IsBanditStoppingTime T),
        Measurable[hT.measurableSpace] ψ →
        IsDeltaCorrect δ (fourWayEnv ![p, p] ![p + s + τ, p + s])
          (fourWayEnv ![p, p] ![p + s + τ + d, p + s]) π T ψ →
        expectedRounds (fourWayEnv ![p, p] ![p + s + τ, p + s]) π T < ⊤ →
        ENNReal.ofReal (BanditAlgorithm.bernoulliRelativeEntropy (1 - δ) δ /
            (τ * Real.log (τ / (τ + d)) +
              (1 - p - s - τ) * Real.log ((1 - p - s - τ) / ((1 - p - s - τ) - d)))) ≤
          expectedRounds (fourWayEnv ![p, p] ![p + s + τ, p + s]) π T := by sorry

end FairReplay.Supplement
