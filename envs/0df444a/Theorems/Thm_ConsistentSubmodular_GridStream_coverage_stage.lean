-- Prove2me | Theorems.Thm_ConsistentSubmodular_GridStream_coverage_stage
-- name    : ConsistentSubmodular.GridStream.coverage_stage
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:50.561222+00:00
-- url     : https://prove2.me/theorems/4e5f7c72-16a4-4008-b2e0-69baba8d3156
-- title:
--   Coverage of the columns of stage $j$
-- statement:
--   Consider the coverage stream $\Sigma$ with budget $k$ and $m$ stages, and let $1\le j\le m$. The set of the $k$ columns $b_{1,j},\dots,b_{k,j}$ of stage $j$ (stream positions $jk\le e<(j+1)k$) has coverage at least $k^2+kj$:
--   $$k\cdot k+k\,j\;\le\;\Bigl|\bigcup_{jk\le e<(j+1)k}\mathrm{cover}(e)\Bigr| .$$
--
--   The columns of stage $j$ cover the whole grid and $j$ auxiliary elements per column, that is $k^2+kj=k(k+j)$ elements, which is the value of the competitor $B_j$ in Appendix B.1.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Impossibility/GridStreamCoverage.lean#L291-L369 (`ConsistentSubmodular.GridStream.coverage_stage`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Impossibility_GridStreamCoverage

open scoped BigOperators
open Finset
open ConsistentSubmodular ConsistentSubmodular.GridStream

theorem ConsistentSubmodular.GridStream.coverage_stage {k m j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m) :
    (k : ℝ) * k + k * j ≤ coverageValue (gridStreamCover k m) (stageColumns k m j) := by sorry
