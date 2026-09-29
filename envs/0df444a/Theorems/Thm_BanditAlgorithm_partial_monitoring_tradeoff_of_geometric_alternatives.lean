-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_tradeoff_of_geometric_alternatives
-- name    : BanditAlgorithm.partial_monitoring_tradeoff_of_geometric_alternatives
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T17:47:59.619916+00:00
-- url     : https://prove2.me/theorems/8f32e1e8-e3f1-4378-9f33-f538925fae5b
-- title:
--   The geometric hard-edge certificate implies the stochastic regret tradeoff
-- statement:
--   Assume a finite partial-monitoring game admits the two geometric alternatives from Theorem 37.12: a feedback-invisible normalized perturbation direction, valid environments $u_a=u-\Delta q$ and $u_b=u+\Delta q$, a uniform loss penalty for actions outside $N_{ab}$, and Eq. (37.10) for actions inside $N_{ab}$. Then there are constants $\varepsilon,\delta>0$ and $C\ge0$ such that, for every horizon $n\ge1$, some $x\ge0$ satisfies
--
--   $$
--   \frac{\varepsilon}{2}x+
--   \frac{n\Delta_n}{8}\exp(-C\Delta_n^2x)
--   \le 2R_n^*(G),
--   \qquad
--   \Delta_n=\delta n^{-1/3}.
--   $$
--
--   Here $x$ is the expected number of actions played outside $N_{ab}$ under the first alternative. This theorem is precisely the KL chain-rule, Bretagnolle–Huber testing, stochastic-to-adversarial minimax layer of the hard-game lower bound.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge UP, 2020), Theorem 37.12, Steps 2–3, printed pp. 490–491, Eqs. (37.8)–(37.10), followed by the Bretagnolle–Huber inequality (Theorem 14.2).

import Definitions.Def_PartialMonitoringGame
import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem BanditAlgorithm.partial_monitoring_tradeoff_of_geometric_alternatives
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊] [DecidableEq 𝕊]
    (G : PartialMonitoringGame k d 𝕊)
    (hgeom : ∃ a b : Fin k, ∃ u q : Fin d → ℝ, ∃ ε δ : ℝ,
      NeighbouringActions G a b ∧ 0 < ε ∧ 0 < δ ∧
      (∑ i, q i) = 0 ∧
      (∑ i, (G.L a i - G.L b i) * q i) = 1 ∧
      (∀ c : Fin k, c ∈ pmNeighbourhood G a b → ∀ σ : 𝕊,
        ∑ i ∈ Finset.univ.filter (fun i ↦ G.Φ c i = σ), q i = 0) ∧
      ∀ Δ : ℝ, 0 < Δ → Δ ≤ δ →
        let ua := fun i ↦ u i - Δ * q i
        let ub := fun i ↦ u i + Δ * q i
        ua ∈ pmCell G a ∧ ub ∈ pmCell G b ∧
        (∀ c : Fin k, c ∉ pmNeighbourhood G a b →
          ε / 2 ≤ ∑ i, (G.L c i - G.L a i) * ua i ∧
          ε / 2 ≤ ∑ i, (G.L c i - G.L b i) * ub i) ∧
        (∀ c : Fin k, c ∈ pmNeighbourhood G a b →
          (∑ i, (G.L c i - G.L a i) * ua i) +
          (∑ i, (G.L c i - G.L b i) * ub i) = Δ)) :
    ∃ ε C δ : ℝ, 0 < ε ∧ 0 ≤ C ∧ 0 < δ ∧
      ∀ (n : ℕ), 1 ≤ n → ∃ x : ℝ, 0 ≤ x ∧
        ε / 2 * x +
            (n : ℝ) * (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) / 8 *
              Real.exp (-C * (δ * (n : ℝ) ^ (-(1 : ℝ) / 3)) ^ 2 * x) ≤
          2 * pmMinimaxRegret G n := by
  sorry
