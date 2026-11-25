-- Prove2me | Theorems.Thm_AdjacencySpectrum_hoffman_ratio
-- name    : AdjacencySpectrum.hoffman_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:47:26.296037+00:00
-- url     : https://prove2.me/theorems/320e2ffa-3220-5665-9213-e84817fc05dd
-- title:
--   Adjacency Spectrum: hoffman ratio
-- statement:
--   **Hoffman's ratio bound.** If a finite graph is `k`-regular with `k ≥ 1`, every independent
--   set has at most `n (−λ_min) / (k − λ_min)` vertices.
--
--   Source: https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/Solution.lean#L56-L59
-- source:
--   https://github.com/jtraverso/spectral-graph-bounds/blob/8d8b4ce17e56165b5f1ad3b285fb141666804e1c/Solution.lean#L56-L59

module
public import Mathlib
public import Definitions.Def_SpectralLib_SpectralBounds
public import Definitions.Def_SpectralGraphBounds_Solution
public import Theorems.Thm_SpectralBounds_hoffman_ratio

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open AdjacencySpectrum
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)

theorem AdjacencySpectrum.hoffman_ratio {k : ℕ} (hk : 1 ≤ k) (hreg : G.IsRegularOfDegree k) {s : Finset V}
    (hs : G.IsIndepSet (s : Set V)) :
    (#s : ℝ) ≤ Fintype.card V * (-(⨅ i, hA.eigenvalues i)) / (k - ⨅ i, hA.eigenvalues i) := by sorry
