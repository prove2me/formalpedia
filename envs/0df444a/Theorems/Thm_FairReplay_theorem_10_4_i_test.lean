-- Prove2me | Theorems.Thm_FairReplay_theorem_10_4_i_test
-- name    : FairReplay.theorem_10_4_i_test
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:49:33.254962+00:00
-- url     : https://prove2.me/theorems/39ac12ac-e05f-42d0-8e41-96c266e9648a
-- title:
--   Theorem 10.4(i), eq. (33) — a four-way test with $\lceil\log\delta/\log(1-d)\rceil$ rounds, zero type-I error
-- statement:
--   Let $p,s,d>0$ with $p+s+d<1$ and $\delta\in(0,1/2)$. In the four-way replay model of the one-edge family (old thresholds $(p,p)$; new thresholds $(p+s,p+s)$ under $H_0$, $(p+s+d,p+s)$ under $H_1$) there is a tester that uses exactly
--
--   $$
--   n_{\mathrm{edge}}=\left\lceil\frac{\log\delta}{\log(1-d)}\right\rceil
--   $$
--
--   rounds, whose decision is measurable for the stopped σ-algebra, and which has zero type-I error and type-II error at most $\delta$:
--
--   $$
--   \mathbb P_0(\text{reject})=0,\qquad \mathbb P_1(\text{not reject})\le\delta .
--   $$
--
--   This is the upper half of part (i): four-way replay detects the patch effect $d$ with order $\log(1/\delta)/d$ rounds.
--
--   **Formalization Note** The stopping time is identically $n_{\mathrm{edge}}$ on every trajectory.
--
--   Differences from the source:
--   - reading: an adaptive tester: actions, stopping time T and accept/reject decision depending on the past transcript → a triple (π, τ, ψ) on the platform's sequential-sampling model: a BanditPolicy over the replay actions, an IsBanditStoppingTime τ (value ⊤ = never stops) and a decision ψ measurable for the stopped σ-algebra; each round's raw ordered outputs are passed as the real number obsCode(outputs); reason: obsCode is injective, so the tester sees the raw ordered transcript; the class is the paper's own 'sequential tester adapted to the independent-round transcript filtration' (Prop. 10.10(i), p.23); randomness outside the transcript (a private seed for τ or ψ) is not modelled, so in the one-action four-way model τ and ψ are functions of the transcript alone
--   - reading: a test using n_edge rounds → τ ω = n_edge for every trajectory ω (a fixed sample size); reason: the stronger of the two readings (rather than τ ≤ n); the paper's tests run exactly n rounds (proof, p.15)
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.4(i), first sentence, eq. (33), p.14 (PDF p.16); proof, p.15

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_FairReplay_fourWayModel

open MeasureTheory

namespace FairReplay

/-- **Theorem 10.4(i), the four-way test, eq. (33)** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027
submission (manuscript of 2026-11-03, sha256 e23940a0…), Theorem 10.4(i), first sentence,
p.14 (PDF p.16)): "Fix p > 0, s > 0, d > 0, p+s+d < 1, and δ ∈ (0, 1/2). [...] (i) Under four-way
counterfactual replay, there is a test using n_edge = ⌈log δ / log(1 − d)⌉ (33) replay rounds with
zero type-I error and type-II error at most δ."

There is a tester `(π, τ, ψ)` on the four-way replay model whose stopping time is identically
`n_edge = ⌈log δ / log(1 − d)⌉`, whose decision is measurable for the stopped σ-algebra, which
never rejects under the null and fails to reject under the alternative with probability at most
`δ`.

**Formalization Note** "A test using n rounds" is a fixed sample size: `τ ω = n_edge` for every
trajectory. A tester is a policy `π` (one action), a stopping time `τ` of the transcript filtration
and a decision `ψ` (`true` = reject); type I is `P₀(τ < ∞ ∧ reject)` and type II is
`P₁(¬(τ < ∞ ∧ reject))`. -/
theorem theorem_10_4_i_test (p s d δ : ℝ) (hp : 0 < p) (hs : 0 < s) (hd : 0 < d)
    (hpsd : p + s + d < 1) (hδ : 0 < δ) (hδ2 : δ < 1 / 2) :
    ∃ (π : BanditAlgorithm.BanditPolicy 1) (τ : (ℕ → Fin 1 × ℝ) → ℕ∞)
      (ψ : (ℕ → Fin 1 × ℝ) → Bool) (hτ : BanditAlgorithm.IsBanditStoppingTime τ),
      Measurable[hτ.measurableSpace] ψ ∧
      (∀ ω, τ ω = ((⌈Real.log δ / Real.log (1 - d)⌉₊ : ℕ) : ℕ∞)) ∧
      BanditAlgorithm.banditTrajMeasure (fourWayModel p s d false) π
          {ω | τ ω < ⊤ ∧ ψ ω = true} = 0 ∧
      BanditAlgorithm.banditTrajMeasure (fourWayModel p s d true) π
          {ω | ¬ (τ ω < ⊤ ∧ ψ ω = true)} ≤ ENNReal.ofReal δ := by sorry

end FairReplay
