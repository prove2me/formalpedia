-- Prove2me | Theorems.Thm_ConsistentSubmodular_GridStream_coverage_le
-- name    : ConsistentSubmodular.GridStream.coverage_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:28.629323+00:00
-- url     : https://prove2.me/theorems/000af50c-4be1-453d-8d8b-513cceb478ac
-- title:
--   Coverage bound on the stream $\Sigma$ (Appendix B.1.2)
-- statement:
--   Consider the coverage stream $\Sigma$ with budget $k$ and $m$ stages, and let $S$ be a set of at most $k$ stream sets. Let $n$ be the number of rows $a_1,\dots,a_k$ in $S$, and let $j\in\mathbb N$ be such that every column set in $S$ comes from a stage at most $j$ (that is, $\lfloor (e-k)/k\rfloor<j$ for every $e\in S$ with $e\ge k$). Then the coverage of $S$ satisfies
--   $$\bigl|\textstyle\bigcup_{e\in S}\mathrm{cover}(e)\bigr|\;\le\; n\,k+(k-n)(k+j)-n\,(k-n),$$
--   with the arithmetic carried out in the reals.
--
--   This is the coverage bound of Appendix B.1.2 used by Lemma 6 and Theorem 3: the $n$ rows cover at most $nk$ cells, and each of the at most $k-n$ remaining sets is a column set covering at most $k+j$ elements, of which $n$ lie in the rows already counted.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Impossibility/GridStreamCoverage.lean#L198-L220 (`ConsistentSubmodular.GridStream.coverage_le`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open Finset
open ConsistentSubmodular

theorem ConsistentSubmodular.GridStream.coverage_le {k m : ℕ} (S : Finset (Fin (k + m * k))) (j : ℕ) (hcard : S.card ≤ k)
    (hj : ∀ e ∈ S, k ≤ e.val → (e.val - k) / k < j) :
    coverageValue (gridStreamCover k m) S ≤
      (rowsHeld k S : ℝ) * k + ((k : ℝ) - rowsHeld k S) * (k + j) -
        rowsHeld k S * ((k : ℝ) - rowsHeld k S) := by sorry
