-- Prove2me | Theorems.Thm_FosterQueues_MG1_theorem3_first_passage_equations
-- name    : FosterQueues.MG1.theorem3_first_passage_equations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:20:16.035334+00:00
-- url     : https://prove2.me/theorems/51bdaed8-099d-43b1-b390-cccd289a8244
-- title:
--   Theorem 3 — the mean first-passage times to 0 of an ergodic system satisfy (6)
-- statement:
--   Let $P=[p_{ij}]$ be the transition matrix of an irreducible, aperiodic Markov chain on $\{0,1,2,\dots\}$ which is ergodic (positive recurrent). For $j\ge0$ let $d_j=\mu_{j0}$ be the mean first-passage time from state $j$ to state $0$. Then $d_j<\infty$ for every $j\ne0$,
--   $$
--   \sum_{j=1}^{\infty}p_{ij}\,d_j = d_i-1 \qquad (i\ne0),
--   $$
--   and
--   $$
--   \sum_{j=1}^{\infty}p_{0j}\,d_j<\infty .
--   $$
--
--   These are the first-step equations for the expected hitting time of state $0$. Foster uses them to show that an ergodic M/G/1 system has $\rho<1$; they are the necessary-condition counterpart of the drift criterion of Theorem 2.
--
--   **Formalization Note** The chain is irreducible and aperiodic by the paper's standing assumption (§1, p. 355). The mean first-passage times are extended nonnegative reals; the conclusion states their finiteness for $j\ne0$ and writes equation (6) in the equivalent form $d_i=1+\sum_{j\ge1}p_{ij}d_j$ in $[0,\infty]$, which avoids subtracting from a possibly infinite quantity. Both sums start at $j=1$, as on the page.
-- source:
--   Foster (Ann. Math. Statist. 24, 1953), Theorem 3, p. 356, eq. (6)

import Mathlib
import Definitions.Def_FosterQueues_MG1_Model

open scoped ENNReal
open QueueingFundamentals.Foundations

namespace FosterQueues.MG1

/-- Foster (1953), Theorem 3, p. 356: if the (irreducible, aperiodic) system is ergodic, the mean
first-passage times `d_j = μ_{j0}` to state `0` are finite for `j ≠ 0` and satisfy
`∑_{j ≥ 1} p_ij d_j = d_i - 1` for `i ≠ 0` (written as `d_i = 1 + ∑_{j ≥ 1} p_ij d_j`) and
`∑_{j ≥ 1} p_0j d_j < ∞`. The sums over `j ≥ 1` are written over `j + 1`, `j : ℕ`. -/
theorem theorem3_first_passage_equations (P : TransitionMatrix) (hirr : P.Irreducible)
    (hap : P.Aperiodic) (herg : P.PositiveRecurrent) :
    (∀ j : ℕ, j ≠ 0 → meanFirstPassage P j 0 < ⊤) ∧
    (∀ i : ℕ, i ≠ 0 → meanFirstPassage P i 0 =
      1 + ∑' j : ℕ, ENNReal.ofReal (P.p i (j + 1)) * meanFirstPassage P (j + 1) 0) ∧
    (∑' j : ℕ, ENNReal.ofReal (P.p 0 (j + 1)) * meanFirstPassage P (j + 1) 0) < ⊤ := by sorry

end FosterQueues.MG1
