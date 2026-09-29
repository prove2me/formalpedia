-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_confidence_union_bound_arithmetic
-- name    : BanditAlgorithm.mdp_confidence_union_bound_arithmetic
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T21:04:08.328421+00:00
-- url     : https://prove2.me/theorems/5aaa9b85-aab1-4ae2-94da-d2b74c245f45
-- title:
--   The union-bound arithmetic behind the UCRL2 confidence radius
-- statement:
--   For $S\ge2$ states, $A\ge1$ actions, horizon $n\ge1$ and $\delta\in(0,1)$,
--   $$SAn\cdot 2^{S}\exp\bigl(-7S\log(2SAn/\delta)\bigr)\le\frac{\delta}{2}.$$
--
--   This is the arithmetic that makes the confidence radius $\sqrt{14S\log(2SAn/\delta)/N}$ of UCRL2 the right one: the exponential is exactly the bound that Weissman's inequality returns at that radius after $N$ observations, the factor $SAn$ counts the state-action pairs and the possible values of the number of observations, and $2^{S}$ is the number of subsets in the categorical concentration inequality.
--
--   Writing $Y=2SAn/\delta\ge4$, the left side is $SAn\cdot2^{S}Y^{-7S}$.  Since $Y\ge4$ one has $2^{S}\le Y^{S/2}$, and $SAn=Y\delta/2$, so the whole expression is at most $(\delta/2)\,Y^{1-13S/2}$, and $1-13S/2\le-12$ for $S\ge2$, so the remaining power of $Y\ge4$ is at most one.  The slack is large: the constant $14$ in the radius is chosen so that this union bound closes with room to spare.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Section 38.6 Step 1, printed pp. 525-526 / PDF pp. 534-535; the radius is Eq. (3) of Jaksch, Ortner and Auer, Near-optimal regret bounds for reinforcement learning, JMLR 11 (2010).

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped NNReal ENNReal

theorem BanditAlgorithm.mdp_confidence_union_bound_arithmetic
    (S A n : ℕ) (hS : 2 ≤ S) (hA : 0 < A) (hn : 0 < n)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    (S : ℝ) * A * n *
        (2 ^ S * Real.exp (-(7 * S * Real.log (2 * S * A * n / δ))))
      ≤ δ / 2 := by
  sorry
