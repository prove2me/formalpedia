-- Prove2me | Theorems.Thm_BianchiIX_empiricalMass_weighted_hasSum
-- name    : BianchiIX.empiricalMass_weighted_hasSum
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T19:07:52.56358+00:00
-- url     : https://prove2.me/theorems/89c7c04c-034b-427d-bb77-31a307725d80
-- title:
--   Weighted empirical masses reproduce a finite sample average
-- statement:
--   For a sequence of labels $\ell:\mathbb N\to I$ and
--   $N\geq0$, define the empirical probability mass
--   $$p_N(i)=\frac1{N+1}\sum_{j=0}^N\mathbf1_{\{\ell_j=i\}}.$$
--
--   For any real function $f$ on $I$, the family $p_N(i)f_i$ has sum
--   $$\sum_{i\in I}p_N(i)f_i=\frac1{N+1}\sum_{j=0}^Nf(\ell_j).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/EmpiricalMass.lean#L23-L32

import Definitions.Def_BianchiIX_Statistics_EmpiricalMass
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open Filter
open scoped Topology
open BianchiIX
noncomputable section
open scoped Classical

theorem BianchiIX.empiricalMass_weighted_hasSum {ι : Type*} (label : ℕ → ι) (N : ℕ) (f : ι → ℝ) :
    HasSum (fun i => empiricalMass label N i * f i)
      (((N + 1 : ℕ) : ℝ)⁻¹ * ∑ j ∈ Finset.range (N + 1), f (label j)) := by sorry
