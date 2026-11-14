-- Prove2me | Theorems.Thm_ConsistentSubmodular_GridStream_card_cover_le
-- name    : ConsistentSubmodular.GridStream.card_cover_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:12.19887+00:00
-- url     : https://prove2.me/theorems/c6e322d9-b710-400c-9439-5fa4dde03403
-- title:
--   Cardinality bound for the cover of a set of grid-stream sets
-- statement:
--   Consider the grid stream with budget $k$ and $m$ stages, whose elements are the positions $0,\dots,k+mk-1$: positions $e<k$ are the rows $a_{e+1}$, and a position $e\ge k$ is a column set of stage $\lfloor (e-k)/k\rfloor+1$ for column $(e-k)\bmod k$. Let $S$ be a set of positions, let $n$ be the number of rows in $S$ and $c$ the number of column sets in $S$ (positions $\ge k$), and let $j\in\mathbb N$ be such that every column set $e\in S$ has $\lfloor (e-k)/k\rfloor<j$ (it comes from a stage at most $j$). Then
--   $$\Bigl|\bigcup_{e\in S}\mathrm{cover}(e)\Bigr|\;\le\; n\,k+c\,(k-n)+c\,j .$$
--
--   The covered grid cells lie in the $n$ rows or, outside them, in the at most $c$ columns of the column sets; the auxiliary elements of column $i$ that are covered are among $u_{i,1},\dots,u_{i,j}$.
--
--   **Formalization Note**: the subtraction $k-n$ is truncated natural subtraction.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Impossibility/GridStreamCoverage.lean#L111-L196 (`ConsistentSubmodular.GridStream.card_cover_le`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Impossibility_GridStreamCoverage

open scoped BigOperators
open Finset
open ConsistentSubmodular ConsistentSubmodular.GridStream

theorem ConsistentSubmodular.GridStream.card_cover_le {k m : ℕ} (S : Finset (Fin (k + m * k))) (j : ℕ)
    (hj : ∀ e ∈ S, k ≤ e.val → (e.val - k) / k < j) :
    (S.biUnion (gridStreamCover k m)).card ≤
      rowsHeld k S * k + columnsHeld k S * (k - rowsHeld k S) + columnsHeld k S * j := by sorry
