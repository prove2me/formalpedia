-- Prove2me | Theorems.Thm_BanditAlgorithm_adversarial_linear_bandit_ftrl_unit_ball_regret_untuned
-- name    : BanditAlgorithm.adversarial_linear_bandit_ftrl_unit_ball_regret_untuned
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T01:33:25.703938+00:00
-- url     : https://prove2.me/theorems/a52c76b1-e03e-47cc-976a-cd18a82cfc37
-- title:
--   Theorem 28.11 core: untuned FTRL unit-ball regret bound
-- statement:
--   This is the untuned regret bound at the end of the proof of Theorem 28.11.
--
--   Fix dimension $d\ge 1$, horizon $n\ge 2$, oblivious loss vectors $y_t$ with $\lVert y_t\rVert_2\le 1$, learning rate $\eta>0$, and shrunken radius
--
--   $$
--   r=1-2\eta d>0.
--   $$
--
--   Let the FTRL iterates use the potential
--
--   $$
--   F(a)=-\log(1-\lVert a\rVert_2)-\lVert a\rVert_2
--   $$
--
--   on the closed ball of radius $r$. At each round, let $V_t$ be uniform on $[0,1]$ and let $W_t$ be uniform on the $2d$ signed coordinate directions. Assume the pairs $(V_t,W_t)$ are mutually independent across rounds and that $V_t$ and $W_t$ are independent within every round. The action explores in direction $W_t$ when $V_t<1-\lVert\bar A_t\rVert_2$, and otherwise plays the radial normalization of $\bar A_t$; the loss estimate is the one-point importance-weighted estimator from Eq. (28.12).
--
--   Then, for every comparator $a_0$ in the Euclidean unit ball,
--
--   $$
--   \mathbb E\!\left[\sum_{t<n}\langle A_t-a_0,y_t\rangle\right]
--   \le
--   (1-r)n+\frac{\log(1/(1-r))}{\eta}+\eta nd.
--   $$
--
--   This parameterized form isolates the stochastic FTRL analysis from the final choice of learning rate and is reusable for alternative tuning rules.
--
--   **Formalization Note** The random exploration seed and signed-direction seed are represented separately. Their within-round independence is stated explicitly in addition to independence of the pairs across rounds.
-- source:
--   Lattimore–Szepesvári, Bandit Algorithms (2020), Theorem 28.11, printed pp. 338–339, especially Eq. (28.12), Eq. (28.14), and the final displayed untuned bound.

import Definitions.Def_OnlineLinearOptimization
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open RealInnerProductSpace MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.adversarial_linear_bandit_ftrl_unit_ball_regret_untuned
    (d n : ℕ) (hd : 0 < d) (hn : 2 ≤ n)
    (y : ℕ → EuclideanSpace ℝ (Fin d)) (hy : ∀ t, ‖y t‖ ≤ 1)
    (η r : ℝ) (hη0 : 0 < η)
    (hr : r = 1 - 2 * η * d) (hr0 : 0 < r)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (V : ℕ → Ω → ℝ) (W : ℕ → Ω → Fin d × Bool)
    (hVmeas : ∀ t, Measurable (V t)) (hWmeas : ∀ t, Measurable (W t))
    (hindep : iIndepFun (fun t ω => (V t ω, W t ω)) P)
    (hVW : ∀ t, IndepFun (V t) (W t) P)
    (hV : ∀ t, Measure.map (V t) P = (volume : Measure ℝ).restrict (Set.Icc 0 1))
    (hW : ∀ t (u : Fin d × Bool), P {ω | W t ω = u} = ((2 * d : ℕ) : ENNReal)⁻¹)
    (Abar A Yhat : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hftrl : ∀ ω, IsFTRLIterates η
      (fun b : EuclideanSpace ℝ (Fin d) => -Real.log (1 - ‖b‖) - ‖b‖)
      (Metric.ball 0 1) (Metric.closedBall 0 r)
      (fun t => Yhat t ω) (fun t => Abar t ω))
    (hA : ∀ t ω, A t ω =
      if V t ω < 1 - ‖Abar t ω‖ then
        (if (W t ω).2 then (1 : ℝ) else -1) • EuclideanSpace.single (W t ω).1 1
      else ‖Abar t ω‖⁻¹ • Abar t ω)
    (hY : ∀ t ω, Yhat t ω =
      (if V t ω < 1 - ‖Abar t ω‖ then
        d * ⟪A t ω, y t⟫ / (1 - ‖Abar t ω‖) else 0) • A t ω) :
    ∀ a₀ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
      ∫ ω, oloRegret (fun t => A t ω) y n a₀ ∂P ≤
        (1 - r) * n + Real.log (1 / (1 - r)) / η + η * n * d := by
  sorry
