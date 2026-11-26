-- Prove2me | Theorems.Thm_Erdos287_sparse_reciprocal_corrections_on_endpoint_windows
-- name    : Erdos287.sparse_reciprocal_corrections_on_endpoint_windows
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T16:30:12.338272+00:00
-- url     : https://prove2.me/theorems/b22342f2-b591-411e-b443-07b524ab6115
-- title:
--   Sparse corrections to a reciprocal sum on an endpoint window
-- statement:
--   For a subset $D$ of an integer interval $[L,U]$ with $L>0$, let $H$ be certified omissions and $R$ certified selections. Suppose a perturbation $c(n)$ vanishes outside the sparse set $S$, which also contains $H$. The corrected reciprocal sum over $D$ is at most $\log((2U+1)/(2L-1))$ plus corrections on $S$. The correction is $-1/n$ on $H$, $c(n)$ on $R$, and $\max(-1/n,c(n))$ at optional positions.
-- source:
--   Erdős #287 finite endpoint-window analysis.

import Mathlib
open Finset

theorem Erdos287.sparse_reciprocal_corrections_on_endpoint_windows (L U : ℕ) (D S H R : Finset ℕ) (c : ℕ → ℝ)
    (hL : 0 < L) (hLU : L ≤ U) (hD : D ⊆ Icc L U) (hS : S ⊆ Icc L U)
    (hH : H ⊆ S) (hdisj : Disjoint D H) (hR : R ⊆ D)
    (hsparse : ∀ n ∈ Icc L U, n ∉ S → c n = 0) :
    (∑ n ∈ D, ((1 : ℝ) / n + c n)) ≤
      Real.log ((2 * (U : ℝ) + 1) / (2 * (L : ℝ) - 1)) +
        ∑ n ∈ S, if n ∈ H then -((1 : ℝ) / n) else
          if n ∈ R then c n else max (-((1 : ℝ) / n)) (c n) := by sorry
