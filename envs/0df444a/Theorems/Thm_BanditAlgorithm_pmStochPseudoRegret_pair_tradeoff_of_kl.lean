-- Prove2me | Theorems.Thm_BanditAlgorithm_pmStochPseudoRegret_pair_tradeoff_of_kl
-- name    : BanditAlgorithm.pmStochPseudoRegret_pair_tradeoff_of_kl
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T19:41:27.197252+00:00
-- url     : https://prove2.me/theorems/5dfb58a6-d64c-4338-8075-9ecf834179b6
-- title:
--   Two-environment partial-monitoring regret tradeoff from KL
-- statement:
--   Fix a partial-monitoring policy $\pi$ and two stochastic environments $u_a,u_b$. Suppose actions $a$ and $b$ are respectively optimal in the two environments. Let $N$ be a neighbourhood of actions. Assume every action outside $N$ has expected loss gap at least $\varepsilon/2$ in both environments, while for every $c\in N$ the two gaps sum to $\Delta$. Let $P_{u_a}^n$ and $P_{u_b}^n$ be the induced history laws. If their KL divergence is finite and satisfies
--
--   $$
--   D(P_{u_a}^n\|P_{u_b}^n)
--   \le C\Delta^2\,\mathbb E_{u_a}[\widetilde T(n)],
--   $$
--
--   where $\widetilde T(n)$ counts actions outside $N$, then there is an $x\ge0$ such that
--
--   $$
--   \frac{\varepsilon}{2}x+
--   \frac{n\Delta}{8}\exp(-C\Delta^2x)
--   \le
--   R_n(\pi,u_a;a)+R_n(\pi,u_b;b).
--   $$
--
--   This is the fixed-policy testing tradeoff in Step 3 of the hard partial-monitoring lower bound. It isolates the regret comparison and Bretagnolle–Huber argument from the preceding geometric construction and adaptive KL calculation.
--
--   **Formalization Note** The two regrets on the right are stochastic pseudo-regrets relative to the designated optimal actions.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge University Press, 2020), Theorem 37.12 proof, Step 3, printed p. 491, Eq. (37.10) and the three displayed regret inequalities using Theorem 14.2.

import Definitions.Def_PartialMonitoringStochastic
import Theorems.Thm_BanditAlgorithm_bretagnolle_huber_inequality_finite_typeStar
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators ENNReal

theorem BanditAlgorithm.pmStochPseudoRegret_pair_tradeoff_of_kl
    {k d n : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊)
    (ua ub : Fin d → ℝ) (hua : ua ∈ stdSimplex ℝ (Fin d))
    (hub : ub ∈ stdSimplex ℝ (Fin d)) (a b : Fin k)
    (N : Finset (Fin k)) (ε C Δ : ℝ)
    (hΔ : 0 < Δ) (hΔε : Δ ≤ ε)
    (haopt : ∀ c : Fin k,
      0 ≤ pmExpectedLoss G ua c - pmExpectedLoss G ua a)
    (hbopt : ∀ c : Fin k,
      0 ≤ pmExpectedLoss G ub c - pmExpectedLoss G ub b)
    (houta : ∀ c : Fin k, c ∉ N →
      ε / 2 ≤ pmExpectedLoss G ua c - pmExpectedLoss G ua a)
    (houtb : ∀ c : Fin k, c ∉ N →
      ε / 2 ≤ pmExpectedLoss G ub c - pmExpectedLoss G ub b)
    (hinside : ∀ c : Fin k, c ∈ N →
      (pmExpectedLoss G ua c - pmExpectedLoss G ua a) +
        (pmExpectedLoss G ub c - pmExpectedLoss G ub b) = Δ)
    (hKLfin : klDiv (pmStochMeasure G π ua hua n)
      (pmStochMeasure G π ub hub n) ≠ ⊤)
    (hKL : (klDiv (pmStochMeasure G π ua hua n)
      (pmStochMeasure G π ub hub n)).toReal ≤
        C * Δ ^ 2 *
          ∫ h, ∑ t : Fin n,
            (if (h t).1 ∉ N then (1 : ℝ) else 0)
            ∂pmStochMeasure G π ua hua n) :
    ∃ x : ℝ, 0 ≤ x ∧
      ε / 2 * x + (n : ℝ) * Δ / 8 *
          Real.exp (-C * Δ ^ 2 * x) ≤
        pmStochPseudoRegret G π ua hua n a +
          pmStochPseudoRegret G π ub hub n b := by
  sorry
