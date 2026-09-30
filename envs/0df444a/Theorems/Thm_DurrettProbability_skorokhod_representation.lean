-- Prove2me | Theorems.Thm_DurrettProbability_skorokhod_representation
-- name    : DurrettProbability.skorokhod_representation
-- status  : Open
-- author  : @naimengye
-- created : 2026-09-19T02:14:28.068959+00:00
-- url     : https://prove2.me/theorems/a70ddb5f-b0c4-4ae2-9f85-e49eaedb0743
-- title:
--   Theorem 8.1.1 — Skorokhod's representation theorem
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb{R}$ with an integrable identity, mean zero, and
--   an integrable square:
--   $$\int x\,d\mu(x)=0,\qquad \int x^2\,d\mu(x)<\infty .$$
--
--   Then there exist a probability space $(\Omega,\mathcal F,\mathbb P)$, a Brownian motion $B$ on
--   it, an increasing family of $\sigma$-fields $F_t\subseteq\mathcal F$ containing the Brownian
--   past $\sigma(B_s:s\le t)$, and a map $T:\Omega\to[0,\infty)$ such that
--
--   1. $T$ is a **stopping time** for that family: $\{T\le t\}\in F_t$ for every $t$;
--   2. the law of $B_T$ is $\mu$;
--   3. $T$ is integrable and $\mathbb ET=\int x^2\,d\mu(x)$.
--
--   Any centred law of finite variance can therefore be realized as the value of a Brownian motion
--   at a stopping time, with expected duration equal to the variance.
--
--   **Formalization Note** The probability space is part of the conclusion rather than a hypothesis.
--   This is what the book's construction does and what it needs: the stopping time is built from an
--   auxiliary pair $(U,V)$ independent of the Brownian motion, so no space carrying only $B$ will
--   do. Durrett flags this himself — "$T_{U,V}$ is not a stopping time for $B_t$ since $(U,V)$ is
--   independent of the Brownian motion" — and works with the enlarged filtration, which is why the
--   statement asks for a family $F_t$ that contains the Brownian past rather than equals it.
--
--   Because the space is produced, the statement also subsumes the existence of a Brownian motion,
--   which the ambient library does not supply.
--
--   The filtration conditions are stated directly: $F$ is monotone, each $F_t$ lies inside the
--   ambient $\sigma$-field, and $\sigma(B_s:s\le t)\subseteq F_t$. The stopping-time property is
--   $\{T\le t\}\in F_t$. Times take values in $[0,\infty)$, so $T$ is finite everywhere and there is
--   no convention about $T=\infty$ to worry about; asserting that $T$ is integrable is part of the
--   claim, not an assumption.
--
--   "The law of $B_T$ is $\mu$" is equality of push-forward measures, which is the book's
--   $B_T=_d X$ with $X$ any random variable of law $\mu$.
-- source:
--   Durrett, Probability: Theory and Examples, Version 5 (11 January 2019), p. 389 (PDF p. 397), Theorem 8.1.1: 'Skorokhod''s representation theorem. If EX = 0 and EX^2 < infinity then there is a stopping time T for Brownian motion so that B_T =d X and ET = EX^2.' Remark: 'The Brownian motion in the statement and all the Brownian motions in this section have B_0 = 0.' Proof, pp. 389-390: 'Suppose first that X is supported on {a, b}, where a < 0 < b. ... If we let T = T_{a,b} = inf{t : B_t not in (a,b)} then Theorem 7.5.3 implies B_T =d X and Theorem 7.5.5 tells us that ET = -ab = EB_T^2.' Durrett also notes: 'Sticklers for detail will notice that T_{U,V} is not a stopping time for B_t since (U,V) is independent of the Brownian motion.' sha256 aeac36cbf5e44c53d69fa60a2d29a393e2d0e8c955ee103bd845d925fd910886

import Mathlib
import Definitions.Def_DurrettProbability_Brownian
import Definitions.Def_DurrettProbability_Donsker

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace DurrettProbability

theorem skorokhod_representation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable id μ) (hmean : ∫ x, x ∂μ = 0)
    (hsq : Integrable (fun x : ℝ => x ^ 2) μ) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : @Measure Ω mΩ) (_ : IsProbabilityMeasure P)
      (B : ℝ≥0 → Ω → ℝ) (F : ℝ≥0 → MeasurableSpace Ω) (T : Ω → ℝ≥0),
      IsBrownianReal B P ∧
      (∀ s t : ℝ≥0, s ≤ t → F s ≤ F t) ∧ (∀ t, F t ≤ mΩ) ∧
      (∀ t, pastSigma B t ≤ F t) ∧
      (∀ t : ℝ≥0, MeasurableSet[F t] {ω | T ω ≤ t}) ∧
      Measure.map (fun ω => B (T ω) ω) P = μ ∧
      Integrable (fun ω => (T ω : ℝ)) P ∧
      ∫ ω, (T ω : ℝ) ∂P = ∫ x : ℝ, x ^ 2 ∂μ := by sorry

end DurrettProbability
