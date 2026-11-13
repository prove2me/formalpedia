-- Prove2me | Theorems.Thm_FairReplay_theorem_10_4_ii_test
-- name    : FairReplay.theorem_10_4_ii_test
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:50:00.403692+00:00
-- url     : https://prove2.me/theorems/67b3475d-0419-4412-8196-c60464e589a2
-- title:
--   Theorem 10.4(ii), eq. (35) — a $\delta$-correct vertex-paired test with $\lceil 2\log(1/\delta)/d^2\rceil$ rounds
-- statement:
--   Let $p,s,d>0$ with $p+s+d<1$ and $\delta\in(0,1/2)$. In the vertex-paired replay model of the one-edge family, even granting the tester $p$, $s$ and the identity of the endpoint $u$ that may receive the differential effect, there is a $\delta$-correct tester that uses exactly
--
--   $$
--   n_{\mathrm{vertex}}=\left\lceil\frac{2\log(1/\delta)}{d^2}\right\rceil
--   $$
--
--   raw vertex-pair rounds, with decision measurable for the stopped σ-algebra.
--
--   This is the upper half of part (ii).
--
--   **Formalization Note** The stopping time is identically $n_{\mathrm{vertex}}$ on every trajectory; $p$, $s$ and the index of $u$ are fixed in the statement, so the tester may use them.
--
--   Differences from the source:
--   - reading: an adaptive tester: actions, stopping time T and accept/reject decision depending on the past transcript → a triple (π, τ, ψ) on the platform's sequential-sampling model: a BanditPolicy over the replay actions, an IsBanditStoppingTime τ (value ⊤ = never stops) and a decision ψ measurable for the stopped σ-algebra; each round's raw ordered outputs are passed as the real number obsCode(outputs); reason: obsCode is injective, so the tester sees the raw ordered transcript; the class is the paper's own 'sequential tester adapted to the independent-round transcript filtration' (Prop. 10.10(i), p.23); randomness outside the transcript (a private seed for τ or ψ) is not modelled, so in the one-action four-way model τ and ψ are functions of the transcript alone
--   - reading: a test using n_vertex rounds → τ ω = n_vertex for every trajectory ω (a fixed sample size); reason: the stronger of the two readings (rather than τ ≤ n); the paper's tests run exactly n rounds (proof, p.15)
--   - reading: δ-correct: both errors at most δ, for a tester 'terminating with a decision' (Prop. 10.10(i)) → IsDeltaCorrect: P₀(τ < ∞ ∧ reject) ≤ δ and P₁(¬(τ < ∞ ∧ reject)) ≤ δ, so non-stopping counts as a type-II error; reason: every tester that terminates with both errors ≤ δ satisfies it, so the lower bounds cover at least the paper's class; it keeps the never-stopping tester out of the upper bounds and of Q
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.4(ii), first sentence, eq. (35), p.14 (PDF p.16); proof, p.15

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_FairReplay_vertexModel
import Definitions.Def_FairReplay_IsDeltaCorrect

open MeasureTheory

namespace FairReplay

/-- **Theorem 10.4(ii), the vertex-paired test, eq. (35)** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027
submission (manuscript of 2026-11-03, sha256 e23940a0…), Theorem 10.4(ii), first
sentence, p.14 (PDF p.16)): "(ii) Under vertex-paired replay, even granting the tester p, s, and the
identity of the endpoint that may receive the differential effect, a δ-correct test exists using
n_vertex = ⌈2 log(1/δ) / d²⌉ (35) raw vertex-pair rounds."

For `p, s, d > 0` with `p + s + d < 1` and `δ ∈ (0, 1/2)`, there is a δ-correct vertex-paired tester
`(π, τ, ψ)` whose stopping time is identically `n_vertex = ⌈2 log(1/δ)/d²⌉` and whose decision is
measurable for the stopped σ-algebra.

**Formalization Note** "A test using n rounds" is a fixed sample size: `τ ω = n_vertex` for every
trajectory. The parameters `p, s` and the identity of `u` (action `0`) are fixed in the statement,
so the tester may depend on them. δ-correctness counts non-stopping as a type-II error. -/
theorem theorem_10_4_ii_test (p s d δ : ℝ) (hp : 0 < p) (hs : 0 < s) (hd : 0 < d)
    (hpsd : p + s + d < 1) (hδ : 0 < δ) (hδ2 : δ < 1 / 2) :
    ∃ (π : BanditAlgorithm.BanditPolicy 2) (τ : (ℕ → Fin 2 × ℝ) → ℕ∞)
      (ψ : (ℕ → Fin 2 × ℝ) → Bool) (hτ : BanditAlgorithm.IsBanditStoppingTime τ),
      Measurable[hτ.measurableSpace] ψ ∧
      (∀ ω, τ ω = ((⌈2 * Real.log (1 / δ) / d ^ 2⌉₊ : ℕ) : ℕ∞)) ∧
      IsDeltaCorrect δ (vertexModel p s d false) (vertexModel p s d true) π τ ψ := by sorry

end FairReplay
