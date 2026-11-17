-- Prove2me | Theorems.Thm_CalibeatBandit_Supplement_theorem_3_6
-- name    : CalibeatBandit.Supplement.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:31:44.370429+00:00
-- url     : https://prove2.me/theorems/8768c487-0d13-4c63-bbb7-80ed471a3372
-- title:
--   Theorem 3.6 — cost of a worst-case guarantee: $\mathbb E[\mathrm{SR}_T],\mathbb E[\mathrm{Rec}_T]\ge T/(44(R_T+\sqrt T))$ although $\mathrm{SR}^{\mathrm{Rec}}_s=0$
-- statement:
--   Consider two actions and a bandit algorithm that reads the recommendation. Suppose it has the worst-case guarantee
--   $$\mathbb E[\mathrm{SR}_T]\le R_T\quad\text{for every recommendation and reward sequence},\qquad R_T=o(T).$$
--
--   **Theorem.** For all sufficiently large $T$ there is a deterministic reward sequence, with recommendation $q_t=e_1$ in every round, such that the recommendation's prefix swap regret vanishes, $\mathrm{SR}^{\mathrm{Rec}}_s=0$ for every $s\le T$, but
--   $$\mathbb E[\mathrm{SR}_T]\ge\frac{T}{44\,(R_T+\sqrt T)},\qquad\mathbb E[\mathrm{Rec}_T]\ge\frac{T}{44\,(R_T+\sqrt T)}.$$
--
--   So a worst-case guarantee $R_T=\tilde O(\sqrt T)$ forces $\tilde\Omega(\sqrt T)$ swap regret on some instance where the recommendation has zero swap regret, and no beyond-worst-case bound is possible. This explains why Algorithm 2's worst-case rate in Theorem 3.5 is weaker than $\tilde O(T^{-1/2})$.
--
--   **Formalization Note** The algorithm is a family $(A_T)_T$ of learners that read the recommendation (`QPolicy 2`), one per horizon, each returning probability vectors. The hypothesis holds for every $T$ and every run of the §2.1 protocol of horizon $T$. The conclusion produces, for all large $T$, a fixed reward sequence and a run of the protocol driven by $A_T$ with these rewards, $q_t=e_1$ and $\mathrm{SR}^{\mathrm{Rec}}_s=0$ on every outcome. $R_T=o(T)$ is `R =o[atTop] (fun T => T)`. $e_1$ is the first action (index $0$).
--
--   Differences from the source:
--
--   - encoding: rounds t = 1, …, T → rounds 0, …, T − 1; reason: Lean convention of the base mission; same instances
--   - generalization: a two-action bandit algorithm → a family (A_T)_T of two-action learners, one per horizon T, each reading q_t and the drawn J_t and returning probability vectors; reason: a single algorithm (which may read q_t, p.7) is the constant family, so the Lean statement specializes to the source; the proof argues for each T separately
--   - reading: R_T = o(T); "for sufficiently large T" → R =o[atTop] (fun T => (T : ℝ)); ∀ᶠ T in atTop; reason: standard meaning of the asymptotic hypotheses
--   - reading: there is a reward sequence with recommendation q_t = e_1 → there is a deterministic oblivious sequence ys and a run of the protocol driven by A_T with y_t = ys_t and q_t = e_1 on every outcome; reason: the stronger of the two readings: the proof ends "By the first moment method, there exists a reward sequence such that the lower bound holds" (p.42), derandomizing its environment G
--   - encoding: for every recommendation and reward sequence → every QProtocolRun of horizon T on every probability space with sample space in a universe u; reason: the base mission's encoding of the §2.1 protocol, with the learner's access to q_t added
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), Theorem 3.6, p.13 (PDF 13); proof in §C.5, pp.40–42 (PDF 40–42)

import Mathlib
import Definitions.Def_CalibeatBandit_IsProbVec
import Definitions.Def_CalibeatBandit_Supplement_QProtocolRun
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_rewardLoss

set_option autoImplicit false

universe u

open MeasureTheory Filter Asymptotics

namespace CalibeatBandit

namespace Supplement

/-- **Theorem 3.6 (Cost of a worst-case guarantee).** Suppose a two-action bandit algorithm
satisfies `E[SR_T] ≤ R_T` for every recommendation and reward sequence, where `R_T = o(T)`. For
sufficiently large `T`, there is a reward sequence with recommendation `q_t = e_1`, such that
`SR^Rec_s = 0` for every `s ≤ T` but
`E[SR_T] ≥ T / (44(R_T + √T))` and `E[Rec_T] ≥ T / (44(R_T + √T))`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), Theorem 3.6,
p.13; proof in §C.5, pp.40–42.

**Formalization Note.** The algorithm is a family `A T` of learners that read the recommendation
(`QPolicy 2`), one per horizon `T` (so it may know `T`); every `A T` returns probability vectors.
The worst-case hypothesis holds for every `T` and every run of the §2.1 protocol of horizon `T`
(every probability space with `Ω : Type u`). The conclusion: eventually in `T` there is a
deterministic oblivious reward sequence `ys` (fixed before the learner's randomness, as the proof's
closing first-moment argument on p.42 produces) and a probability space with a run of horizon `T`
driven by `A T` whose rewards are `ys`, with `q_t = e_1` (the first action, index `0`) in every
round and every outcome, `SR^Rec_s = swapRegret s y J = 0` for every `s ≤ T` and every outcome,
and both expectation bounds. `SR_T`, `Rec_T` are the base
`swapRegret`, `rewardLoss`; `E` is the Bochner integral. -/
theorem theorem_3_6 (A : ℕ → QPolicy 2)
    (hA : ∀ T t q J I r, IsProbVec (A T t q J I r))
    (R : ℕ → ℝ) (hR : R =o[atTop] (fun T : ℕ => (T : ℝ)))
    (hworst : ∀ (T : ℕ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (run : QProtocolRun 2 T P (A T)),
      ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P ≤ R T) :
    ∀ᶠ T : ℕ in atTop, ∃ ys : ℕ → Fin 2 → ℝ, ∃ (Ω : Type u) (_ : MeasurableSpace Ω)
      (P : Measure Ω), IsProbabilityMeasure P ∧ ∃ run : QProtocolRun 2 T P (A T),
        (∀ t < T, ∀ ω, run.y t ω = ys t) ∧
        (∀ t < T, ∀ ω, run.q t ω = Pi.single 0 1) ∧
        (∀ s ≤ T, ∀ ω, swapRegret s (fun t => run.y t ω) (fun t => run.J t ω) = 0) ∧
        (T : ℝ) / (44 * (R T + Real.sqrt T))
          ≤ ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P ∧
        (T : ℝ) / (44 * (R T + Real.sqrt T))
          ≤ ∫ ω, rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω)
              (fun t => run.I t ω) ∂P := by sorry

end Supplement

end CalibeatBandit
