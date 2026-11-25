-- Prove2me | Theorems.Thm_AdjacencySpectrum_le_maxDegree
-- name    : AdjacencySpectrum.le_maxDegree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:35:45.071825+00:00
-- url     : https://prove2.me/theorems/a2459a8f-4123-5153-981f-295681ce5bd5
-- title:
--   Adjacency Spectrum: le max Degree
-- statement:
--   The largest adjacency eigenvalue is at most the maximum degree.
--
--   Source: https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/Solution.lean#L40-L41
-- source:
--   https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/Solution.lean#L40-L41

module
public import Mathlib
public import Definitions.Def_SpectralLib_SpectralBounds
public import Definitions.Def_SpectralGraphBounds_Solution
public import Theorems.Thm_SpectralBounds_le_maxDegree

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open AdjacencySpectrum
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)

theorem AdjacencySpectrum.le_maxDegree : ⨆ i, hA.eigenvalues i ≤ G.maxDegree := by sorry
