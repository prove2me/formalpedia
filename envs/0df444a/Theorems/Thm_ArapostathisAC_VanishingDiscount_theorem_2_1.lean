-- Prove2me | Theorems.Thm_ArapostathisAC_VanishingDiscount_theorem_2_1
-- name    : ArapostathisAC.VanishingDiscount.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:41:22.001958+00:00
-- url     : https://prove2.me/theorems/6c2c842a-3b65-4dce-bbbe-3f7b61e2ad3a
-- title:
--   Theorem 2.1 (i), (iii) — the discounted cost optimality equation and a discount optimal stationary policy
-- statement:
--   Consider the countable-state controlled Markov process of §5 and fix a discount factor $0<\beta<1$. Then
--
--   1. the discounted value function satisfies the **discounted cost optimality equation** (DCOE)
--   $$J^*_\beta(i)=\inf_{a\in U(i)}\Big\{c(i,a)+\beta\sum_{j\in S}P(j\mid i,a)\,J^*_\beta(j)\Big\},\qquad i\in S;$$
--   2. there is a stationary deterministic policy $f\in\Pi_{SD}$ that is $\beta$-discount optimal: $J_\beta(i,f)=J^*_\beta(i)$ for every $i\in S$.
--
--   The DCOE is the starting point of the vanishing discount approach: the equation (5.6) for $h_\beta$ is obtained from it by subtracting $J^*_\beta(0)$.
--
--   **Formalization Note.** The paper states Theorem 2.1 for Borel state and action spaces under Assumptions 2.1–2.3 and cites it without proof. In the countable model these assumptions follow from the standing assumptions of §5: Assumption 2.2 (weak continuity of $P$) holds because on a countable state space weak continuity of $a\mapsto P(\cdot\mid i,a)$ is continuity of each $a\mapsto P(j\mid i,a)$; Assumption 2.3 holds because every compact-valued multifunction on a discrete space is upper semicontinuous and $c(i,\cdot)$ is continuous and nonnegative. Values are in $[0,\infty]$, where the equation holds even when $J^*_\beta$ takes the value $+\infty$, and the infimum in the policy class runs over all history-dependent randomized admissible policies. Parts (ii), (iv) and (v) of the theorem are not stated here.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 289, Theorem 2.1 (i), (iii), (2.7); countable form on p. 301

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_DPMaps

namespace ArapostathisAC.VanishingDiscount

theorem theorem_2_1 {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) :
    (∀ i, discValue M β i = discBellman M β (discValue M β) i) ∧
    ∃ f : StationaryPolicy M, IsDiscOptimal M β f := by sorry

end ArapostathisAC.VanishingDiscount
