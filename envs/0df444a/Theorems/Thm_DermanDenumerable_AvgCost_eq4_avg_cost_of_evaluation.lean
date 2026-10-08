-- Prove2me | Theorems.Thm_DermanDenumerable_AvgCost_eq4_avg_cost_of_evaluation
-- name    : DermanDenumerable.AvgCost.eq4_avg_cost_of_evaluation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:19:35.646869+00:00
-- url     : https://prove2.me/theorems/1a3d695e-723b-4f3c-ad71-41d23dddd494
-- title:
--   (4) — a rule of C'' solving (2) with bounded v has average cost g
-- statement:
--   Let $I$ be a denumerable state space with finite decision sets and bounded costs $w_{ik}$ (conditions (A) and (B)). Let $R \in C''$ be a stationary deterministic rule making decision $k_i$ at state $i$, write $p_{ij} = q_{ij}(k_i)$, and suppose that a number $g$ and a bounded set of numbers $\{v_j\}_{j \in I}$ satisfy equation (2):
--   $$g + v_i = w_{ik_i} + \sum_{j \in I} p_{ij} v_j, \qquad i \in I.$$
--   Then for every initial state $i'$ the expected average cost converges to $g$:
--   $$\lim_{T\to\infty} \frac{1}{T+1}\sum_{t=0}^{T} E_R W_t = g, \qquad \text{in particular} \quad Q_R(i') = g .$$
--
--   This is display (4) of the paper: $g$ is the expected average cost per unit time under $R$. It holds for every rule of $C''$ that solves (2) with a bounded $v$, and no recurrence condition is needed. It is used in the proof of Theorem 1 for the minimizing rule $R^*$, and in Lemma 1 as $g = Q_R(l)$.
--
--   **Formalization Note.** The statement asserts both that the limit exists and that it equals $g$; $Q_R(i')$ is the `limsup` of the averages. The bounded $v$ is part of the hypothesis, as in the paper (the interchange of summation in (3) relies on it).
-- source:
--   Derman, Denumerable State Markovian Decision Processes—Average Cost Criterion, Ann. Math. Statist. 37(6) (1966), p. 1549, §3, display (4) (from (2), (3) on p. 1548)

import Mathlib
import Definitions.Def_DermanDenumerable_AvgCost_Model
open scoped Topology
open Filter SennottDP.AvgFinite

namespace DermanDenumerable.AvgCost

/-- Derman (1966), §3, display (4), p. 1549: if the rule `e ∈ C''` (decision `k_i = e.f i`) and a
bounded `{v_j}` satisfy (2) with the number `g`, then for every initial state `i` the expected
average cost `(T + 1)^{-1} Σ_{t=0}^{T} E_e W_t` converges to `g`; in particular `Q_e(i) = g`. -/
theorem eq4_avg_cost_of_evaluation {S Act : Type} [Countable S] (M : MDC S Act)
    (w : S → Act → ℝ) (hB : CostBounded M w) (e : StationaryPolicy M) (g : ℝ) (v : S → ℝ)
    (hv : BddFun v) (hD : IsEvaluation M w e g v) :
    ∀ i : S,
      Tendsto (fun T : ℕ => ((T : ℝ) + 1)⁻¹ *
          ∑ t ∈ Finset.range (T + 1), expCostR e.toPolicy w i t) atTop (𝓝 g) ∧
        avgCostR e.toPolicy w i = g := by sorry

end DermanDenumerable.AvgCost
