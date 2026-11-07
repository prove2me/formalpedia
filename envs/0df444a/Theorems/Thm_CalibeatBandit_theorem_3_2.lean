-- Prove2me | Theorems.Thm_CalibeatBandit_theorem_3_2
-- name    : CalibeatBandit.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:43:29.889049+00:00
-- url     : https://prove2.me/theorems/2041fd94-4c49-472b-9521-95e503b94ea3
-- title:
--   Theorem 3.2 — bandit calibeating: $\mathbb E[\mathrm{SR}_T]\le r_T+\sqrt{2TK\log K}$, $\mathbb E[\mathrm{Rec}_T]\le r_T$, and $\tilde O(K^2\varepsilon^{-2})$ rounds
-- statement:
--   Instantiate all internal learners of the bandit feedback calibeating algorithm (Algorithm 1 with the exploration, reward estimation and feedback modifications of §3.2) by exponential weights (3.3) with learning rate $\eta$, starting from uniform weights.
--
--   1. If $K\ge1$, $\eta>0$, $0<\mu\le\frac12$ and $\mu\ge4K\eta$, then in every run of the interaction protocol (adaptive and randomized recommendations and rewards, possibly correlated through information unavailable to the learner, fixed before the learner's draws of each round)
--   $$\mathbb E[\mathrm{SR}_T]\le r_T+\sqrt{2TK\log K},\qquad\mathbb E[\mathrm{Rec}_T]\le r_T,\qquad r_T=\mu T+\frac{2K\log K+\log 2}{\eta}+\frac{5\eta KT}{1-\mu}.$$
--   2. In other words, under the same conditions the algorithm is $(\alpha,\beta)$-calibeating over $T$ rounds with $\alpha=\frac{r_T}T+\sqrt{\frac{2K\log K}T}$ and $\beta=\frac{r_T}T$.
--   3. With the parameters $\eta^*=\min\{\frac1{8K},\sqrt{\frac{2K\log K+\log2}{14KT}}\}$ and $\mu^*=4K\eta^*$ of the proof, there is an absolute constant $C>0$ such that for every $K\ge1$, $\varepsilon>0$ and $T\ge CK^2\log K/\varepsilon^2$ the algorithm is $(\varepsilon,\varepsilon)$-calibeating over $T$ rounds; that is, $(\varepsilon,\varepsilon)$-calibeating is achieved in $\tilde O(K^2\varepsilon^{-2})$ rounds.
--
--   The learner sees only the reward of the action it plays, yet competes simultaneously with every post-processing of its own actions (swap regret) and with every post-processing of the recommended actions (reward loss), at rate $\tilde O(K\sqrt T)$.
--
--   **Formalization Note** $\mathrm{SR}_T$ and $\mathrm{Rec}_T$ are the realized benchmarks of the run; the probability spaces range over an arbitrary universe.
--
--   Differences from the source:
--   - reading: $\log$ → the natural logarithm `Real.log`; reason: p.7 fixes $e$ as the base of the natural logarithm, and the proof's $K\log K=\log K^K$ counts the $K^K$ post-processing rules
--   - reading: "With suitable parameters, $(\varepsilon,\varepsilon)$-calibeating is achievable in $\tilde O(K^2\varepsilon^{-2})$ rounds" → there is $C>0$ such that for all $K\ge1$, $\varepsilon>0$ and every $T\ge CK^2\log K/\varepsilon^2$ the algorithm with the proof's $\eta^*,\mu^*$ (p.36) is $(\varepsilon,\varepsilon)$-calibeating over $T$ rounds; reason: the parameters are the ones the proof chooses; the polylogarithmic factor of $\tilde O$ is the $\log K$ of $r_T$, and the bound holds for every horizon beyond the threshold
--   - encoding: "for every recommendation and reward sequence satisfying the interaction protocol" → every `ProtocolRun` on every probability space in a universe `u`: σ-algebras $\mathcal E_t$ of everything fixed before the learner's round-$t$ draws, $q_t,y_t$ $\mathcal E_t$-measurable, $P(J_t=j\mid\mathcal E_t)=q_t(j)$, $P(I_t=i\mid\mathcal E_t\vee\sigma(J_t))=p_t(i)$; the constant $C$ is chosen after `u`; reason: this is §2.1's protocol with Algorithm 1's draw of $J_t$; adaptive, randomized and correlated environments are all instances
--   - encoding: $x_t$, "the mixed strategy solving Equation (3.1)" → the explicit $(1-\lambda_t)(I-\lambda_tM^{\mathrm{SR}}_t)^{-1}M^{\mathrm{Rec}}_te_{J_t}$; reason: $\lambda_t\in(0,1)$, so (3.1) has exactly this solution, which lies in $\Delta(\mathcal A)$
--   - encoding: $\alpha=r_T/T+\sqrt{2K\log K/T}$, $\beta=r_T/T$ → the same with Lean's $x/0=0$; reason: at $T=0$ both sides of Definition 2.2's inequalities are $0$; for $T\ge1$ the expressions are the paper's
--   - encoding: $\mathbb E[\cdot]$ → the Bochner integral against $P$; reason: the integrands are bounded measurable functions of the run, so the integrals are the expectations
--   - encoding: rounds $t=1,\dots,T$, actions $\mathcal A=[K]$ → rounds $t=0,\dots,T-1$ (`Finset.range T`), actions `Fin K`; reason: a relabelling; same instances
--   - encoding: the action set $[K]$ of a positive integer $K$ and the learning rate $\eta>0$ of (3.3) → explicit hypotheses $0<K$, $0<\eta$; reason: the paper states these once, on p.7 and in (3.3); no instance changes
--   - encoding: the learner "has access to the recommendation $q_t$" and draws $J_t\sim q_t$ (Algorithm 1) → the policy receives the drawn $J_t$ and not $q_t$; reason: the algorithm uses $q_t$ only to draw $J_t$; the protocol still gives $J_t$ the conditional law $q_t$
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), Theorem 3.2, p.11 (PDF 11); the parameters of its last sentence from the proof, §C.2, p.36 (PDF 36)

import Mathlib
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Definitions.Def_CalibeatBandit_IsCalibeating
import Definitions.Def_CalibeatBandit_rT
import Definitions.Def_CalibeatBandit_etaStar

set_option autoImplicit false

universe u

open MeasureTheory Matrix

namespace CalibeatBandit

/-- **Theorem 3.2 (Bandit calibeating).** Instantiate all internal learners of the bandit
feedback algorithm (Algorithm 1 with the modifications of §3.2) by exponential weights (3.3) with
learning rate `η`, starting from uniform weights. If `0 < μ ≤ 1/2` and `μ ≥ 4Kη`, then
`E[SR_T] ≤ r_T + √(2TK log K)` and `E[Rec_T] ≤ r_T`, where
`r_T = μT + (2K log K + log 2)/η + 5ηKT/(1 − μ)`. In other words, the algorithm is
`(α, β)`-calibeating with `α = r_T/T + √(2K log K/T)` and `β = r_T/T`. With suitable parameters,
`(ε, ε)`-calibeating is achievable in `Õ(K²ε⁻²)` rounds.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), Theorem 3.2, p.11; the parameters of the last sentence are those of the proof, p.36.

**Formalization Note.** Three conjuncts.
1. For every `K ≥ 1`, `T`, `η > 0`, `μ` with `0 < μ ≤ 1/2` and `4Kη ≤ μ`, every probability space
   and every run of the §2.1 protocol (`ProtocolRun`: adaptive, randomized environment whose
   `q_t`, `y_t` may be correlated through information the learner never sees, fixed before the
   learner's round-`t` draws) driven by `calibeatPolicy K η μ`, the two inequalities hold, with
   `E` the Bochner integral and `SR_T`, `Rec_T` the realized benchmarks.
2. The "in other words" restatement through Definition 2.2 (`IsCalibeating`).
3. The `Õ(K²ε⁻²)` clause, pinned as: there is an absolute constant `C > 0` such that for all
   `K ≥ 1`, `ε > 0` and `T ≥ C K² log K / ε²`, the algorithm with the proof's parameters
   `η* = min{1/(8K), √((2K log K + log 2)/(14KT))}`, `μ* = 4Kη*` (p.36) is `(ε, ε)`-calibeating
   over `T` rounds.
`log` is `Real.log` (p.7: `e` is the base of the natural logarithm); actions are `Fin K`; rounds
are `0, …, T − 1`. Probability spaces range over `Type u` for an arbitrary universe `u`. -/
theorem theorem_3_2 :
    (∀ (K T : ℕ) (η μ : ℝ), 0 < K → 0 < η → 0 < μ → μ ≤ 1 / 2 → 4 * K * η ≤ μ →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (run : ProtocolRun K T P (calibeatPolicy K η μ)),
        ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P
            ≤ rT K T η μ + Real.sqrt (2 * T * K * Real.log K) ∧
        ∫ ω, rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω) ∂P
            ≤ rT K T η μ) ∧
    (∀ (K T : ℕ) (η μ : ℝ), 0 < K → 0 < η → 0 < μ → μ ≤ 1 / 2 → 4 * K * η ≤ μ →
      IsCalibeating.{u} K T (rT K T η μ / T + Real.sqrt (2 * K * Real.log K / T))
        (rT K T η μ / T) (calibeatPolicy K η μ)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (K T : ℕ) (ε : ℝ), 0 < K → 0 < ε →
      C * K ^ 2 * Real.log K / ε ^ 2 ≤ T →
      IsCalibeating.{u} K T ε ε (calibeatPolicy K (etaStar K T) (muStar K T))) := by sorry

end CalibeatBandit
