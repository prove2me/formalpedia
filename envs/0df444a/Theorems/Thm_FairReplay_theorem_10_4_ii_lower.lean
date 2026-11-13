-- Prove2me | Theorems.Thm_FairReplay_theorem_10_4_ii_lower
-- name    : FairReplay.theorem_10_4_ii_lower
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:49:34.343268+00:00
-- url     : https://prove2.me/theorems/ca2b0c95-a4b6-4b8b-a97e-7055b0796a8a
-- title:
--   Theorem 10.4(ii), eq. (36) — every $\delta$-correct vertex-paired tester has $\mathbb E_0[T]\ge\mathrm{kl}(1-\delta,\delta)/K_{\mathrm{vertex}}$
-- statement:
--   Let $p,s,d>0$ with $p+s+d<1$, $\delta\in(0,1/2)$ and $r=1-p-s$. Every adaptive $\delta$-correct vertex-paired tester with finite expected stopping time — choosing $u$ or $v$ in every round, adaptively and possibly at random — satisfies
--
--   $$
--   \mathbb E_0[T]\ \ge\ \frac{\mathrm{kl}(1-\delta,\delta)}{s\log\frac{s}{s+d}+r\log\frac{r}{r-d}} .
--   $$
--
--   This is the lower half of part (ii). Since the denominator is $\frac{d^2}{2}\bigl(\frac1s+\frac1r\bigr)+O(d^3)$, it matches the vertex-paired test (35) up to constants.
--
--   Differences from the source:
--   - reading: an adaptive tester: actions, stopping time T and accept/reject decision depending on the past transcript → a triple (π, τ, ψ) on the platform's sequential-sampling model: a BanditPolicy over the replay actions, an IsBanditStoppingTime τ (value ⊤ = never stops) and a decision ψ measurable for the stopped σ-algebra; each round's raw ordered outputs are passed as the real number obsCode(outputs); reason: obsCode is injective, so the tester sees the raw ordered transcript; the class is the paper's own 'sequential tester adapted to the independent-round transcript filtration' (Prop. 10.10(i), p.23); randomness outside the transcript (a private seed for τ or ψ) is not modelled, so in the one-action four-way model τ and ψ are functions of the transcript alone
--   - reading: δ-correct: both errors at most δ, for a tester 'terminating with a decision' (Prop. 10.10(i)) → IsDeltaCorrect: P₀(τ < ∞ ∧ reject) ≤ δ and P₁(¬(τ < ∞ ∧ reject)) ≤ δ, so non-stopping counts as a type-II error; reason: every tester that terminates with both errors ≤ δ satisfies it, so the lower bounds cover at least the paper's class; it keeps the never-stopping tester out of the upper bounds and of Q
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.4(ii), second sentence, eq. (36), p.14 (PDF p.16)

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_FairReplay_vertexModel
import Definitions.Def_FairReplay_IsDeltaCorrect
import Definitions.Def_FairReplay_expectedRounds

open MeasureTheory

namespace FairReplay

/-- **Theorem 10.4(ii), the vertex-paired lower bound, eq. (36)** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027
submission (manuscript of 2026-11-03, sha256 e23940a0…), Theorem 10.4(ii),
second sentence, p.14 (PDF p.16)): "Conversely, every adaptive δ-correct vertex-paired tester with
finite expected stopping time satisfies E0[T] ≥ kl(1 − δ, δ) / (s log(s/(s+d)) + r log(r/(r−d))).
(36)"

For `p, s, d > 0` with `p + s + d < 1` and `δ ∈ (0, 1/2)`, every δ-correct vertex-paired tester
`(π, τ, ψ)` with `E₀[τ] < ∞` has `E₀[τ] ≥ kl(1 − δ, δ) / (s log(s/(s + d)) + r log(r/(r − d)))`,
`r = 1 − p − s`.

**Formalization Note** The tester chooses `u` (action `0`) or `v` (action `1`) adaptively, possibly
at random, in every round; `τ` is a stopping time of the transcript filtration and `ψ` is measurable
for the stopped σ-algebra. δ-correctness counts non-stopping as a type-II error. -/
theorem theorem_10_4_ii_lower (p s d δ : ℝ) (hp : 0 < p) (hs : 0 < s) (hd : 0 < d)
    (hpsd : p + s + d < 1) (hδ : 0 < δ) (hδ2 : δ < 1 / 2)
    (π : BanditAlgorithm.BanditPolicy 2) (τ : (ℕ → Fin 2 × ℝ) → ℕ∞)
    (ψ : (ℕ → Fin 2 × ℝ) → Bool) (hτ : BanditAlgorithm.IsBanditStoppingTime τ)
    (hψ : Measurable[hτ.measurableSpace] ψ)
    (hcorr : IsDeltaCorrect δ (vertexModel p s d false) (vertexModel p s d true) π τ ψ)
    (hfin : expectedRounds (vertexModel p s d false) π τ < ⊤) :
    ENNReal.ofReal (BanditAlgorithm.bernoulliRelativeEntropy (1 - δ) δ /
        (s * Real.log (s / (s + d)) +
          (1 - p - s) * Real.log ((1 - p - s) / ((1 - p - s) - d)))) ≤
      expectedRounds (vertexModel p s d false) π τ := by sorry

end FairReplay
