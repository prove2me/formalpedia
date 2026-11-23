-- Prove2me | Theorems.Thm_ArapostathisAC_VanishingDiscount_Supplement_theorem_5_8
-- name    : ArapostathisAC.VanishingDiscount.Supplement.theorem_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:09:55.481434+00:00
-- url     : https://prove2.me/theorems/d5727a3f-a176-4c02-be2f-739d47a1dcfb
-- title:
--   Theorem 5.8 — under the Lyapunov condition of Assumption 5.13 an AC-optimal $f\in\Pi_{SD}$ exists
-- statement:
--   In the countable-state model of §5 with nonnegative, possibly unbounded costs, let $\tilde P(f)(i,j)=P(f)(i,j)$ for $j\ne0$ and $\tilde P(f)(i,0)=0$. Suppose there is $w:S\to\mathbb R_+$ such that for all $i$:
--
--   1. $c(i,f(i))+1+\sum_j\tilde P(f)(i,j)w(j)\le w(i)$ for every $f\in\Pi_{SD}$;
--   2. $\sum_jP(f)(i,j)w(j)$ is continuous in $f$;
--   3. $\lim_{n\to\infty}\sum_j\tilde P^n(f)(i,j)w(j)=0$.
--
--   Then there is an AC-optimal $f\in\Pi_{SD}$: $J(i,f)=J^*(i)$ for every $i$.
--
--   **Formalization Note** $\tilde P^n(f)(i,j)$ is the probability that $X_1,\dots,X_n\ne0$ and $X_n=j$; all sums involving $w$ are computed in $[0,\infty]$, and continuity in $f$ is sequential in the product topology on $\Pi_{SD}$.
--
--   Differences from the source:
--   - encoding: sums ∑_j P̃(f)(i, j) w(j) and ∑_j P(f)(i, j) w(j) as real numbers → sums in [0, ∞]; reason: the terms are nonnegative; (i) makes them finite
--   - encoding: continuity in f → sequential continuity in the product topology on Π_SD; reason: the product of countably many metric spaces is metrizable
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 306, Theorem 5.8 and Assumption 5.13

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_StationaryChain
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_Recurrence

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open ArapostathisAC.VanishingDiscount

namespace ArapostathisAC.VanishingDiscount.Supplement

/-- Theorem 5.8 (p. 306). Under the Lyapunov condition of Assumption 5.13 (possibly unbounded
nonnegative costs), there exists an AC-optimal `f ∈ Π_SD`. -/
theorem theorem_5_8 {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (hL : Assumption513 M) :
    ∃ f : StationaryPolicy M, IsAvgOptimal M f := by sorry

end ArapostathisAC.VanishingDiscount.Supplement
