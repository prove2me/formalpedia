-- Prove2me | Theorems.Thm_FairReplay_Supplement_theorem_10_5_eq_49_50
-- name    : FairReplay.Supplement.theorem_10_5_eq_49_50
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:54:59.963194+00:00
-- url     : https://prove2.me/theorems/7d2305e0-facd-4824-b9dc-94a29adb6071
-- title:
--   Theorem 10.5, eqs. (49)–(50) — the composite problem $|p_{1,u}-p_{1,v}|\le\tau$ vs. $\ge\tau+d$ has a fixed-design test with $\lceil 8(\tau+d)\log(1/\delta)/d^2\rceil$ rounds
-- statement:
--   Let $\tau\ge0$, $d>0$ with $\tau+d<1$, and $\delta\in(0,1/2)$. The composite problem
--   $$H_0:\ |p_{1,u}-p_{1,v}|\le\tau,\qquad H_1:\ |p_{1,u}-p_{1,v}|\ge\tau+d,$$
--   over all old and new thresholds in $[0,1]$, admits a fixed-design four-way synchronized-replay test using at most
--   $$\Big\lceil\frac{8(\tau+d)\log(1/\delta)}{d^2}\Big\rceil$$
--   rounds: it rejects with probability at most $\delta$ under every instance of $H_0$ and fails to reject with probability at most $\delta$ under every instance of $H_1$.
--
--   This is the upper bound matching the lower bound (48) up to constants when $r-d$ is bounded below.
--
--   Differences from the source:
--   - generalization: P18 parameters p > 0, s ≥ 0 with p + s + τ + d < 1 → only τ ≥ 0, d > 0, τ + d < 1 assumed; reason: the composite problem (49) involves only τ and d; every P18 instance satisfies the Lean hypotheses
--   - encoding: fixed-design test using at most N rounds → ∃ N ≤ ⌈8(τ+d) log(1/δ)/d²⌉ with T ≡ N; four-way replay has a single action, so the schedule is fixed; reason: fixed design = fixed sample size
--   - encoding: thresholds of the composite problem → all old and new thresholds in [0, 1]; the tester does not depend on them; reason: thresholds are probabilities
--   - encoding: an adaptive (δ-correct) tester → a triple (π, T, ψ) on the published sequential-sampling model: possibly randomized adaptive policy, stopping time of the transcript filtration (⊤ = never stops), decision measurable for the stopped σ-algebra; type II counts non-stopping as an error; reason: the tester model of the published base mission; randomized policies contain the deterministic ones, so the class is at least the paper's
--   - encoding: the round reveals its ordered raw Boolean outputs → the output vector is passed to the model through the injective real code obsCode; laws are images of the uniform tape on [0, 1]; reason: an injective code loses no information, so the tester sees the whole transcript
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.5, eqs. (49)–(50), p.16 (PDF p.18)

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_FairReplay_Supplement_fourWayEnv
import Definitions.Def_FairReplay_Supplement_Qthr

open MeasureTheory

namespace FairReplay.Supplement

/-- **Theorem 10.5, eqs. (49)–(50), the composite fixed-design test** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0…), Theorem 10.5, p.16
(PDF p.18)): "Conversely, the full composite problem H0 : |p1,u − p1,v| ≤ τ, H1 : |p1,u − p1,v| ≥ τ + d
(49) admits a fixed-design synchronized-replay test using at most ⌈8(τ + d) log(1/δ) / d²⌉ (50)
rounds."

For `τ ≥ 0`, `d > 0` with `τ + d < 1` and `δ ∈ (0, 1/2)`, there are a four-way tester `(π, T, ψ)` and a
number `N ≤ ⌈8(τ + d) log(1/δ)/d²⌉` with `T ≡ N`, such that for all old thresholds and all new
thresholds in `[0, 1]`: if the new endpoint gap `|p1,u − p1,v|` is at most `τ` the test rejects with
probability at most `δ`, and if it is at least `τ + d` the test fails to reject with probability at most
`δ`.

**Formalization Note** Four-way replay has a single action, so every policy plays the same schedule;
"fixed-design" is the fixed sample size `T ≡ N`. The test may not depend on the thresholds. The
composite problem involves only `τ` and `d`, so the P18 parameters `p, s` do not appear; `τ + d < 1` is
implied by `p + s + τ + d < 1`. -/
theorem theorem_10_5_eq_49_50 (τ d δ : ℝ) (hτ : 0 ≤ τ) (hd : 0 < d) (hτd : τ + d < 1)
    (hδ : 0 < δ) (hδ2 : δ < 1 / 2) :
    ∃ (π : BanditAlgorithm.BanditPolicy 1) (T : (ℕ → Fin 1 × ℝ) → ℕ∞)
      (ψ : (ℕ → Fin 1 × ℝ) → Bool) (hT : BanditAlgorithm.IsBanditStoppingTime T) (N : ℕ),
      Measurable[hT.measurableSpace] ψ ∧ (∀ ω, T ω = (N : ℕ∞)) ∧
      N ≤ ⌈8 * (τ + d) * Real.log (1 / δ) / d ^ 2⌉₊ ∧
      IsThrCompositeCorrect τ d δ π T ψ := by sorry

end FairReplay.Supplement
