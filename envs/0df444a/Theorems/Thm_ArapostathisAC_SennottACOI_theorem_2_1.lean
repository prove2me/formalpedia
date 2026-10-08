-- Prove2me | Theorems.Thm_ArapostathisAC_SennottACOI_theorem_2_1
-- name    : ArapostathisAC.SennottACOI.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:24:32.297696+00:00
-- url     : https://prove2.me/theorems/39560183-e33c-47c9-a8bc-ab0437fb402a
-- title:
--   Theorem 2.1 (i), (iii) — the discounted cost optimality equation and a discount optimal stationary policy (countable states)
-- statement:
--   Consider the countable-state controlled Markov process of §5: states $S=\{0,1,2,\dots\}$, nonempty compact admissible action sets $U(i)$, a nonnegative cost $c(i,a)$ and transition probabilities $P(j\mid i,a)$, both continuous in $a\in U(i)$. Let $\beta\in(0,1)$ and let $J^*_\beta(i)=\inf_{\pi\in\Pi}J_\beta(i,\pi)\in[0,\infty]$ be the optimal discounted cost over all admissible policies. Then:
--
--   1. the **discounted cost optimality equation** (DCOE) holds: for every $i\in S$,
--   $$J^*_\beta(i)=\inf_{a\in U(i)}\Big\{c(i,a)+\beta\sum_{j\in S}P(j\mid i,a)\,J^*_\beta(j)\Big\};$$
--   2. there is a stationary deterministic policy $f\in\Pi_{SD}$ that is $\beta$-discount optimal, i.e. $J_\beta(i,f)=J^*_\beta(i)$ for every $i\in S$.
--
--   This is the countable-state instance of the paper's Theorem 2.1 (i) and (iii); the paper states it for Borel state spaces under Assumptions 2.1–2.3, which hold in the §5 model (discrete state space, compact $U(i)$, continuity of $c(i,\cdot)$ and $P(j\mid i,\cdot)$). It provides the $\beta_n$-discount optimal policies $f_{\beta_n}$ from which the proof of Theorem 5.9 starts.
--
--   **Formalization Note** Both sides of the DCOE are computed in $[0,\infty]$, so the equation is meaningful even where $J^*_\beta$ is infinite; the integral $\int_S J^*_\beta(y)P(dy\mid x,a)$ of the paper is the series $\sum_j P(j\mid i,a)J^*_\beta(j)$ on the countable state space. Part (ii) of the paper's theorem (characterization of discount optimal policies) is not part of this item.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 289, Theorem 2.1 (i), (iii), display (2.7); specialised to the countable model of §5, p. 299

import Mathlib
import Definitions.Def_ArapostathisAC_SennottACOI_CMP

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ArapostathisAC.SennottACOI

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

/-- Theorem 2.1 (i), (iii) (p. 289) for the countable-state model of §5: for every discount
factor `β ∈ (0, 1)` the discounted value function satisfies the discounted cost optimality
equation (2.7), `J*_β(i) = inf_{a ∈ U(i)} {c(i, a) + β Σ_j P(j | i, a) J*_β(j)}`, computed in
`[0, ∞]`, and a `β`-discount optimal stationary deterministic policy exists. -/
theorem theorem_2_1 (M : ArapostathisAC.VanishingDiscount.CMP A) (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) :
    (∀ i, ArapostathisAC.VanishingDiscount.discValue M β i =
      ⨅ a ∈ M.U i, (ENNReal.ofReal (M.c i a) +
        ENNReal.ofReal β * ∑' j, M.P (i, a) {j} * ArapostathisAC.VanishingDiscount.discValue M β j)) ∧
    ∃ f : StationaryPolicy M, ArapostathisAC.VanishingDiscount.IsDiscOptimal M β f := by sorry

end ArapostathisAC.SennottACOI
