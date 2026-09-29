-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_hopeless_globally_invisible_alternatives_of_outside
-- name    : BanditAlgorithm.partial_monitoring_hopeless_globally_invisible_alternatives_of_outside
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T16:40:44.658416+00:00
-- url     : https://prove2.me/theorems/14911b65-e2e8-4848-a23e-ecf26c34dca0
-- title:
--   Globally feedback-invisible alternatives around a non-observable edge
-- statement:
--   Let $a,b$ be neighbouring actions whose loss difference is not globally observable, and suppose their neighbourhood does not contain every action. Then there are globally feedback-indistinguishable a positive interior distribution $u$, a feedback-invisible direction $q$, and constants $\varepsilon,\delta>0$ such that every sufficiently small symmetric perturbation $u_a=u-\Delta q$ and $u_b=u+\Delta q$ stays in the cells of $a$ and $b$. Actions outside the neighbourhood retain a uniform loss gap at least $\varepsilon/2$, while for every action $c$ in the neighbourhood the two suboptimality gaps sum exactly to $\Delta$.
--
--   The direction is invisible to every action, not only the neighbourhood. This packages the finite-cell stability and interpolation geometry needed to turn global non-observability into two statistically indistinguishable stochastic environments.
--
--   **Formalization Note** The theorem returns the selected edge again so that its conclusion has the same reusable shape as the geometric-alternatives node used for the hard-game lower bound.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), Theorems 37.12–37.13, perturbation and regret geometry in Eqs. (37.5)–(37.10), printed pp. 488–492 (PDF pp. 496–500); https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringGame
import Theorems.Thm_BanditAlgorithm_partial_monitoring_nonglobal_edge_direction
import Theorems.Thm_BanditAlgorithm_partial_monitoring_uniform_outside_gap
import Theorems.Thm_BanditAlgorithm_partial_monitoring_neighbour_positive_common_point
import Theorems.Thm_BanditAlgorithm_partial_monitoring_neighbour_loss_interpolation
import Theorems.Thm_stdSimplex_small_perturbation
import Theorems.Thm_finite_linear_gaps_stable
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic

open Set

theorem BanditAlgorithm.partial_monitoring_hopeless_globally_invisible_alternatives_of_outside
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [DecidableEq 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (a b : Fin k)
    (hab : NeighbouringActions G a b)
    (hn_global : ¬ ∃ f : Fin k × 𝕊 → ℝ, IsGlobalLossEstimator G a b f)
    (hout : ∃ c : Fin k, c ∉ pmNeighbourhood G a b) :
    ∃ a b : Fin k, ∃ u q : Fin d → ℝ, ∃ ε δ : ℝ,
      NeighbouringActions G a b ∧ 0 < ε ∧ 0 < δ ∧
      (∑ i, q i) = 0 ∧
      (∑ i, (G.L a i - G.L b i) * q i) = 1 ∧
      (∀ c : Fin k, ∀ σ : 𝕊,
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
          (∑ i, (G.L c i - G.L b i) * ub i) = Δ) := by
  sorry
