-- Prove2me | Theorems.Thm_AdjacencySpectrum_average_degree_le
-- name    : AdjacencySpectrum.average_degree_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:41:15.031979+00:00
-- url     : https://prove2.me/theorems/00f5f4bf-5acf-536c-b63d-2835bb2bc380
-- title:
--   Adjacency Spectrum: average degree le
-- statement:
--   The average degree `2 |E| / n` is at most the largest adjacency eigenvalue.
--
--   Source: https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/Solution.lean#L35-L37
-- source:
--   https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/Solution.lean#L35-L37

module
public import Mathlib
public import Definitions.Def_SpectralLib_SpectralBounds
public import Definitions.Def_SpectralGraphBounds_Solution
public import Theorems.Thm_SpectralBounds_average_degree_le

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open AdjacencySpectrum
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)

theorem AdjacencySpectrum.average_degree_le :
    2 * (#G.edgeFinset : ℝ) / Fintype.card V ≤ ⨆ i, hA.eigenvalues i := by sorry
