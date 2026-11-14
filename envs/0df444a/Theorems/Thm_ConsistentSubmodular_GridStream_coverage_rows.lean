-- Prove2me | Theorems.Thm_ConsistentSubmodular_GridStream_coverage_rows
-- name    : ConsistentSubmodular.GridStream.coverage_rows
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:25.539906+00:00
-- url     : https://prove2.me/theorems/4a79dd0f-3ddb-4664-9e18-da623a79c6ac
-- title:
--   The $k$ rows cover the whole grid
-- statement:
--   Consider the coverage stream $\Sigma$ with budget $k$ and $m$ stages. The set of the first $k$ stream elements, the rows $a_1,\dots,a_k$, has coverage at least $k^2$:
--   $$k\cdot k\;\le\;\Bigl|\bigcup_{e<k}\mathrm{cover}(e)\Bigr| .$$
--
--   The rows $a_1,\dots,a_k$ cover the whole $k\times k$ grid $U_{\mathrm{core}}$. Together with the bound on rows alone, this gives the value $k^2$ of the optimum after the rows have arrived.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Impossibility/GridStreamCoverage.lean#L243-L263 (`ConsistentSubmodular.GridStream.coverage_rows`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open Finset
open ConsistentSubmodular

theorem ConsistentSubmodular.GridStream.coverage_rows {k m : ℕ} :
    (k : ℝ) * k ≤ coverageValue (gridStreamCover k m) (arrivedPrefix (k + m * k) k) := by sorry
