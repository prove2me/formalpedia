-- Prove2me | Theorems.Thm_ConsistentSubmodular_HardInstance_weighted_main
-- name    : ConsistentSubmodular.HardInstance.weighted_main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:25:00.86003+00:00
-- url     : https://prove2.me/theorems/507583a9-b7f5-49fb-8735-f1aaafaf920c
-- title:
--   Weighted hard stream: every randomized consistent algorithm loses a factor $\rho$ at one of the last three times
-- statement:
--   Let $k,C\in\mathbb N$ with $k\ge2$, and let $x,\rho\in\mathbb R$ with $x>0$, $x(1+x)\le1$ and $\rho\ge0$. Consider the hard stream on $3k+2$ elements with the weights $1,\;x,\;x^2(1+x)$ for the three groups, and let $f$ be the weighted coverage. Assume that
--   $$k\,N(x)+E(x)\,C\;\le\;\rho\,\bigl(k\,D(x)-E(x)\bigr),$$
--   where $N,D,E$ are the numerator, denominator and error term of the linear program. Then for every randomized algorithm $\mu$ all of whose realizations are feasible with cardinality budget $k$ and change budget $C$, there are a time $t\in\{0,\dots,3k+2\}$ and a family $A\subseteq X_t$ with $|A|\le k$ that covers all $k$ cells of group $0$ (the competitor covers all of $U_0$), such that
--   $$\mathbb E_\mu\bigl[f(\mathrm{ALG}_t)\bigr]\le\rho\,f(A).$$
--
--   This is the argument of Appendix A.2 on the stream with the weights $1,x,x^2(1+x)$: if $\rho$ satisfies the inequality of the linear program, then no $C$-consistent randomized algorithm has expected value better than $\rho$ times that of a competitor at one of the three last times.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Impossibility/HardInstance.lean#L161-L281 (`ConsistentSubmodular.HardInstance.weighted_main`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Impossibility_HardInstance

open scoped BigOperators
open Finset
open ConsistentSubmodular ConsistentSubmodular.HardInstance

theorem ConsistentSubmodular.HardInstance.weighted_main {k C : ℕ} {x ρ : ℝ} (hk : 2 ≤ k) (hx0 : 0 < x) (hx1 : x * (1 + x) ≤ 1)
    (hρ0 : 0 ≤ ρ)
    (hρ : (k : ℝ) * lpNumerator x + lpError x * C ≤ ρ * (k * lpDenominator x - lpError x))
    (μ : RandomTrajectory (3 * k + 2)) (hμ : μ.Feasible k C) :
    ∃ (t : Fin (3 * k + 2 + 1)) (A : Finset (Fin (3 * k + 2))),
      A ⊆ arrivedPrefix (3 * k + 2) t.val ∧ A.card ≤ k ∧
      (k : ℝ) ≤ (fiber (A.biUnion (elementCells k)) 0).card ∧
      μ.expectation (weightedValue k (lpWeights x)) t ≤ ρ * weightedValue k (lpWeights x) A := by sorry
