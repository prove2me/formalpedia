-- Prove2me | Theorems.Thm_BianchiIX_empiricalMass_hasSum
-- name    : BianchiIX.empiricalMass_hasSum
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T19:11:18.31877+00:00
-- url     : https://prove2.me/theorems/e59d99d5-5b03-47c5-b69a-2f51f8972af9
-- title:
--   Normalization of the empirical distribution
-- statement:
--   For a sequence of labels $\ell:\mathbb N\to I$ and
--   $N\geq0$, define the empirical probability mass
--   $$p_N(i)=\frac1{N+1}\sum_{j=0}^N\mathbf1_{\{\ell_j=i\}}.$$
--   The empirical masses have convergent sum
--   $$\sum_{i\in I}p_N(i)=1.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/EmpiricalMass.lean#L34-L37

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

theorem BianchiIX.empiricalMass_hasSum {ι : Type*} (label : ℕ → ι) (N : ℕ) :
    HasSum (empiricalMass label N) 1 := by sorry
