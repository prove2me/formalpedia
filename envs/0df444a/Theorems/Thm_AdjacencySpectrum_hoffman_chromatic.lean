-- Prove2me | Theorems.Thm_AdjacencySpectrum_hoffman_chromatic
-- name    : AdjacencySpectrum.hoffman_chromatic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:46:37.422079+00:00
-- url     : https://prove2.me/theorems/2d4c6a36-4952-5cf5-b491-0e1f27949c79
-- title:
--   Adjacency Spectrum: hoffman chromatic
-- statement:
--   **Hoffman's bound (1970).** If a finite graph has at least one edge, every proper colouring
--   with `c` colours satisfies `1 - λ_max / λ_min ≤ c`.
--
--   Source: https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/Solution.lean#L50-L52
-- source:
--   https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/Solution.lean#L50-L52

module
public import Mathlib
public import Definitions.Def_SpectralLib_SpectralBounds
public import Definitions.Def_SpectralGraphBounds_Solution
public import Theorems.Thm_SpectralBounds_hoffman_chromatic

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open AdjacencySpectrum
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)

theorem AdjacencySpectrum.hoffman_chromatic (hE : G.edgeSet.Nonempty) {c : ℕ} (hc : G.Colorable c) :
    1 - (⨆ i, hA.eigenvalues i) / (⨅ i, hA.eigenvalues i) ≤ c := by sorry
