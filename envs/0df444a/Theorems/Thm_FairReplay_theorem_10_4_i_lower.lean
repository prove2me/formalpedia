-- Prove2me | Theorems.Thm_FairReplay_theorem_10_4_i_lower
-- name    : FairReplay.theorem_10_4_i_lower
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:49:40.790999+00:00
-- url     : https://prove2.me/theorems/383b07ef-0b94-4133-b018-2f252e3c0ff3
-- title:
--   Theorem 10.4(i), eq. (34) — every $\delta$-correct four-way tester has $\mathbb E_0[T]\ge\mathrm{kl}(1-\delta,\delta)/(r\log\frac{r}{r-d})$
-- statement:
--   Let $p,s,d>0$ with $p+s+d<1$, $\delta\in(0,1/2)$ and $r=1-p-s$. Every adaptive $\delta$-correct tester for the four-way replay model of the one-edge family with finite expected stopping time satisfies, on the null,
--
--   $$
--   \mathbb E_0[T]\ \ge\ \frac{\mathrm{kl}(1-\delta,\delta)}{r\log\frac{r}{r-d}} .
--   $$
--
--   This is the lower half of part (i). Since $r\log\frac{r}{r-d}=d+O(d^2)$, it matches the four-way test (33) up to constants.
--
--   Differences from the source:
--   - reading: an adaptive tester: actions, stopping time T and accept/reject decision depending on the past transcript → a triple (π, τ, ψ) on the platform's sequential-sampling model: a BanditPolicy over the replay actions, an IsBanditStoppingTime τ (value ⊤ = never stops) and a decision ψ measurable for the stopped σ-algebra; each round's raw ordered outputs are passed as the real number obsCode(outputs); reason: obsCode is injective, so the tester sees the raw ordered transcript; the class is the paper's own 'sequential tester adapted to the independent-round transcript filtration' (Prop. 10.10(i), p.23); randomness outside the transcript (a private seed for τ or ψ) is not modelled, so in the one-action four-way model τ and ψ are functions of the transcript alone
--   - reading: δ-correct: both errors at most δ, for a tester 'terminating with a decision' (Prop. 10.10(i)) → IsDeltaCorrect: P₀(τ < ∞ ∧ reject) ≤ δ and P₁(¬(τ < ∞ ∧ reject)) ≤ δ, so non-stopping counts as a type-II error; reason: every tester that terminates with both errors ≤ δ satisfies it, so the lower bounds cover at least the paper's class; it keeps the never-stopping tester out of the upper bounds and of Q
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.4(i), second sentence, eq. (34), p.14 (PDF p.16); proof eq. (41), p.15

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_FairReplay_fourWayModel
import Definitions.Def_FairReplay_IsDeltaCorrect
import Definitions.Def_FairReplay_expectedRounds

open MeasureTheory

namespace FairReplay

/-- **Theorem 10.4(i), the four-way lower bound, eq. (34)** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027
submission (manuscript of 2026-11-03, sha256 e23940a0…), Theorem 10.4(i), second
sentence, p.14 (PDF p.16); proof eq. (41), p.15): "Every adaptive δ-correct tester with finite
expected stopping time satisfies, on the null, E0[T] ≥ kl(1 − δ, δ) / (r log(r/(r−d))),
r = 1 − p − s. (34)"

For `p, s, d > 0` with `p + s + d < 1` and `δ ∈ (0, 1/2)`, every δ-correct four-way tester
`(π, τ, ψ)` with `E₀[τ] < ∞` has `E₀[τ] ≥ kl(1 − δ, δ) / (r log(r/(r − d)))`, `r = 1 − p − s`.

**Formalization Note** Testers are arbitrary adaptive (possibly randomized) policies with a
stopping time of the transcript filtration and a decision measurable for the stopped σ-algebra;
δ-correctness counts non-stopping as a type-II error. `kl` is
`BanditAlgorithm.bernoulliRelativeEntropy`. -/
theorem theorem_10_4_i_lower (p s d δ : ℝ) (hp : 0 < p) (hs : 0 < s) (hd : 0 < d)
    (hpsd : p + s + d < 1) (hδ : 0 < δ) (hδ2 : δ < 1 / 2)
    (π : BanditAlgorithm.BanditPolicy 1) (τ : (ℕ → Fin 1 × ℝ) → ℕ∞)
    (ψ : (ℕ → Fin 1 × ℝ) → Bool) (hτ : BanditAlgorithm.IsBanditStoppingTime τ)
    (hψ : Measurable[hτ.measurableSpace] ψ)
    (hcorr : IsDeltaCorrect δ (fourWayModel p s d false) (fourWayModel p s d true) π τ ψ)
    (hfin : expectedRounds (fourWayModel p s d false) π τ < ⊤) :
    ENNReal.ofReal (BanditAlgorithm.bernoulliRelativeEntropy (1 - δ) δ /
        ((1 - p - s) * Real.log ((1 - p - s) / ((1 - p - s) - d)))) ≤
      expectedRounds (fourWayModel p s d false) π τ := by sorry

end FairReplay
