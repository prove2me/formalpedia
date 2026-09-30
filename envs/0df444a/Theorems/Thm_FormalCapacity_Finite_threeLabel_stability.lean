-- Prove2me | Theorems.Thm_FormalCapacity_Finite_threeLabel_stability
-- name    : FormalCapacity.Finite.threeLabel_stability
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-07T21:59:52.851718+00:00
-- url     : https://prove2.me/theorems/60f89e83-ab73-4dce-bfe2-228e8eb39cce
-- title:
--   Three-label one-sided stability for block scores
-- statement:
--   Let $f_1,f_2,f_3$, the four block intensities $\beta_{123},\beta_{12},\beta_{23},\beta_{13}$, the deficits $d_{12},d_{23},d_{13}$, and the weights $q_{12},q_{23}$ be real numbers. Assume all four block intensities are nonnegative and satisfy the marginal capacity inequalities
--
--   $$
--   \beta_{123}+\beta_{12}+\beta_{13}\le f_1,\qquad
--   \beta_{123}+\beta_{12}+\beta_{23}\le f_2,\qquad
--   \beta_{123}+\beta_{13}+\beta_{23}\le f_3.
--   $$
--
--   Assume also
--
--   $$
--   \begin{aligned}
--   d_{12}&=\min(f_1,f_2)-\beta_{123}-\beta_{12},\\
--   d_{23}&=\min(f_2,f_3)-\beta_{123}-\beta_{23},\\
--   d_{13}&=\min(f_1,f_3)-\beta_{123}-\beta_{13},
--   \end{aligned}
--   \qquad
--   0\le q_{12},q_{23}\le1,\quad q_{12}+q_{23}\ge1,\quad f_2\ge\min(f_1,f_3).
--   $$
--
--   Define $\gamma_{123}=\min(f_1,\min(f_2,f_3))$, $\gamma_{12}=\max(\min(f_1,f_2)-f_3,0)$, $\gamma_{23}=\max(\min(f_2,f_3)-f_1,0)$, and $S_q(x)=x_{123}+q_{12}x_{12}+q_{23}x_{23}$. Then both bounds hold:
--
--   $$
--   S_q(\gamma)-d_{12}-d_{23}\le S_q(\beta)\le S_q(\gamma)+d_{13}.
--   $$
--
--   The inequality controls downward score loss using only the two adjacent deficits and upward score gain using only the outer-pair deficit. It is a pointwise real-algebraic statement: no measure, normalization, coupling-existence hypothesis, or strict ordering of the densities is required. Zero intensities, tied densities, and boundary weights are included.
-- source:
--   Interval-Möbius capacity and temporal block flow, unpublished project note (2026), Lemma 3.1, equation (3.3), with block capacities and deficits in equations (2.2)–(2.4); CAPACITY_FLOW_THEOREM.md SHA-256 700d20415a4a673e5b27b1e6d508a89204afb85dfe54daddf8d4d84b1492d15f. Exact formal source: formal_capacity/FormalCapacity/Finite/ThreeLabel.lean, declaration FormalCapacity.Finite.threeLabel_stability, lines 66–215 (including its source docstring). Source-file SHA-256 6fdb4ddc257384df9f6df0a8f7c6083a32828efd6c2c0d06857e83cb1b204bb0. Source ranges are compiler-derived. Local source archive; no public repository URL, commit, or externally established authorship is asserted. Upload checked with Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Definitions.Def_capacityThreeLabel

set_option autoImplicit false

/-!
# The three-label scalar stability inequality

This file formalizes the finite, pointwise heart of the temporal capacity-flow
argument.  It contains no measure theory and no stochastic assumptions.

The variables `beta123`, `beta12`, `beta23`, and `beta13` are nonnegative
block intensities at one density point.  The three `cap` assumptions say that
the blocks using a label cannot exceed that label's available density.  The
`dij` variables are the pairwise maximality deficits.
-/

open FormalCapacity.Finite

theorem FormalCapacity.Finite.threeLabel_stability
    {f1 f2 f3 beta123 beta12 beta23 beta13 d12 d23 d13 q12 q23 : ℝ}
    (_hbeta123 : 0 ≤ beta123)
    (hbeta12 : 0 ≤ beta12)
    (hbeta23 : 0 ≤ beta23)
    (hbeta13 : 0 ≤ beta13)
    (hcap1 : beta123 + beta12 + beta13 ≤ f1)
    (hcap2 : beta123 + beta12 + beta23 ≤ f2)
    (hcap3 : beta123 + beta13 + beta23 ≤ f3)
    (hd12 : d12 = min f1 f2 - beta123 - beta12)
    (hd23 : d23 = min f2 f3 - beta123 - beta23)
    (hd13 : d13 = min f1 f3 - beta123 - beta13)
    (_hq12_nonneg : 0 ≤ q12)
    (hq12_le_one : q12 ≤ 1)
    (_hq23_nonneg : 0 ≤ q23)
    (hq23_le_one : q23 ≤ 1)
    (hq_sum : 1 ≤ q12 + q23)
    (hmiddle : min f1 f3 ≤ f2) :
    canonicalScore q12 q23 f1 f2 f3 - d12 - d23 ≤
        threeScore q12 q23 beta123 beta12 beta23 ∧
      threeScore q12 q23 beta123 beta12 beta23 ≤
        canonicalScore q12 q23 f1 f2 f3 + d13 := by
  sorry
