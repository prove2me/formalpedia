-- Prove2me | Theorems.Thm_FewExperts_Supplement_theorem_7_adaptive_lower_bound
-- name    : FewExperts.Supplement.theorem_7_adaptive_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:57:06.680239+00:00
-- url     : https://prove2.me/theorems/121abca0-5462-4e6c-b44f-22d148c65f5c
-- title:
--   Theorem 7 — $\Omega(T)$ subscriptions are needed against adaptive adversaries
-- statement:
--   Consider prediction with expert advice with $N$ experts and horizon $T$. An adaptive adversary chooses the gains $g_t\in[0,1]^N$ of round $t$ as a function of the experts $a_1,\dots,a_{t-1}$ the learner played earlier.
--
--   There is a constant $c>0$ with the following property. Let $2\le T\le N$, and let $\mathcal A$ be a randomized online algorithm, with randomness $\omega\sim\mu$ and measurable in $\omega$, that at round $t$ sees $\omega$ and the gains of rounds $1,\dots,t-1$. Suppose that against every adaptive adversary the expected realized regret is at most $T/2$:
--   $$\mathbb E_\omega\Bigl[\max_i\sum_{t=1}^Tg_t^i-\sum_{t=1}^Tg_t^{a_t}\Bigr]\le\frac T2 .$$
--   Then there is an adaptive adversary against which
--   $$\mathbb E_\omega\bigl[\,|\{a_1,\dots,a_T\}|\,\bigr]\ge c\cdot T.$$
--
--   Every expert played must be subscribed to. Against adaptive adversaries, low regret therefore forces linearly many subscriptions, so the polylogarithmic upper bound of Theorem 4 genuinely depends on the adversary being oblivious.
--
--   Differences from the source:
--   - generalization: expected regret at most T/2 against every adaptive adversary → expected regret at most T/2 against every adaptive adversary that is a deterministic function of the learner's past actions; reason: a weaker hypothesis on a subclass of the paper's adversaries; the proof's adversary belongs to it, so the Lean theorem implies the printed one
--   - generalization: must subscribe to Ω(T) distinct experts in expectation → the expected number of distinct experts played in rounds 1..T is at least c·T; reason: every played expert is subscribed, so the Lean bound implies the printed one
--   - encoding: any (randomized) algorithm → any probability space (Ω, μ) of type Type* and A : OnlineAlg Ω N measurable in ω for each round and history; a [NeZero N] binder; reason: every randomized online algorithm draws its randomness once; NeZero N holds since N ≥ T ≥ 2
--   - encoding: Ω(·) → ∃ c > 0 chosen before N, T and the algorithm; reason: standard reading
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), Theorem 7, p.34 (PDF p.35)

import Mathlib
import Definitions.Def_FewExperts_Supplement_adaptivePlay

namespace FewExperts.Supplement

open MeasureTheory

/-- **Theorem 7: Ω(T) subscriptions against adaptive adversaries.**
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), Theorem 7, p.34 (PDF 35): "For 2 ≤ T ≤ N, any algorithm with expected regret at most
T/2 against every adaptive adversary must subscribe to Ω(T) distinct experts in expectation on
some input."

There is a constant `c > 0` such that for all `2 ≤ T ≤ N`, every randomized online algorithm `A`
(any probability space `(Ω, μ)`, `A` measurable in its randomness) whose expected regret is at most
`T/2` against every adaptive adversary with gains in `[0, 1]` satisfies, against some such
adversary, `E[number of distinct experts played in rounds 1, …, T] ≥ c · T`.

**Formalization Note** An adaptive adversary chooses the gains of round `t` as a deterministic
function of the experts played in rounds `1, …, t − 1`; the regret is that of the realized gains
and plays (`adaptiveGains`, `adaptivePlay`). Every played expert is subscribed, so the lower bound
on the experts played implies the paper's bound on subscriptions. -/
theorem theorem_7_adaptive_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ N T : ℕ, 2 ≤ T → T ≤ N → ∀ [NeZero N],
      ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (A : LimitedSwitching.HighProb.OnlineAlg Ω N),
        (∀ (t : ℕ) (past : Fin (t - 1) → Fin N → ℝ), Measurable (fun ω => A ω t past)) →
        (∀ adv : AdaptiveAdv N, IsAdaptiveAdv T adv →
          ∫ ω, gainRegret T (adaptiveGains A adv ω) (adaptivePlay A adv ω) ∂μ ≤ (T : ℝ) / 2) →
        ∃ adv : AdaptiveAdv N, IsAdaptiveAdv T adv ∧
          c * (T : ℝ) ≤ ∫ ω, (numPlayed T (adaptivePlay A adv ω) : ℝ) ∂μ := by sorry

end FewExperts.Supplement
