-- Prove2me | Theorems.Thm_ConsistentSubmodular_GridStream_coverage_le_rows
-- name    : ConsistentSubmodular.GridStream.coverage_le_rows
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:45.809219+00:00
-- url     : https://prove2.me/theorems/c516257d-2c74-4308-a1b1-424536b3d21e
-- title:
--   Coverage of rows only is at most $nk$
-- statement:
--   Consider the coverage stream $\Sigma$ with budget $k$ and $m$ stages, and let $S$ be a set of stream positions contained in the first $k$ positions (that is, $S$ consists only of rows $a_1,\dots,a_k$ and contains no column sets). Let $n$ be the number of rows in $S$. Then
--   $$\bigl|\textstyle\bigcup_{e\in S}\mathrm{cover}(e)\bigr|\;\le\; n\,k .$$
--
--   With no column sets, each row covers exactly the $k$ cells of its grid row, so $n$ rows cover at most $nk$ elements.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Impossibility/GridStreamCoverage.lean#L222-L241 (`ConsistentSubmodular.GridStream.coverage_le_rows`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open Finset
open ConsistentSubmodular

theorem ConsistentSubmodular.GridStream.coverage_le_rows {k m : ℕ} (S : Finset (Fin (k + m * k)))
    (hS : S ⊆ arrivedPrefix (k + m * k) k) :
    coverageValue (gridStreamCover k m) S ≤ (rowsHeld k S : ℝ) * k := by sorry
