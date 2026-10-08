-- Prove2me | Theorems.Thm_CirclePackingConstants_sixteen_cover_g2a
-- name    : CirclePackingConstants.sixteen_cover_g2a
-- status  : Proved
-- author  : @vebis
-- created : 2026-10-06T15:07:36.678062+00:00
-- url     : https://prove2.me/theorems/fad97fd3-1881-4b0d-8dd8-4c473cc3d523
-- title:
--   Covering of the count vectors with $(n_0,n_1,n_2)\in\{(0,1,0), (0,1,2)\}$ by library patterns
-- statement:
--   Let $n_0,\dots,n_{15}$ be the numbers of points of a sixteen-point configuration in the sixteen cells of the $4\times4$ subdivision of the unit square (cell $Q_{xy}$ has index $i=4x+y$), with $n_i\le 2$, $\sum_i n_i=16$ and not all $n_i=1$. Suppose $(n_0,n_1,n_2)$ is one of the listed triples. Then some pattern of the library `sixteenLib`, placed by a symmetry of the square and a translation by whole cells, is dominated by the counts: there are $e,s,tx,ty$ with `Matches sixteenLib n e s tx ty`.
--
--   This is a part of the combinatorial covering of the count vectors $\{0,1,2\}^{16}$ by library patterns: a depth-first search over a partial assignment of the counts, branching on cells and stopping as soon as a library pattern is contained in the partial assignment. It refines the covering statements for a given $(n_0,n_1)$ into the cases of the third cell, so that every certificate is small.
--
--   **Formalization Note.** `Sixteen.Matches` and `Sixteen.sixteenLib` are defined in `CirclePackingConstants_SixteenOcc`; the proof is a kernel-checked certificate (`decide +kernel`) of the depth-first search, with soundness proved in `CirclePackingConstants_SixteenGlue` and `CirclePackingConstants_SixteenPieces`.
-- source:
--   G. Wengerodt, Die dichteste Packung von 16 Kreisen in einem Quadrat, Beitraege zur Algebra und Geometrie 16 (1983), 173-190 (optimality of the 4x4 grid); the occupancy-pattern decomposition, the pattern library and the certificates are computer generated for this formalization.

import Definitions.Def_CirclePackingConstants
import Definitions.Def_CirclePackingConstants_SixteenOcc

noncomputable section

namespace CirclePackingConstants

theorem sixteen_cover_g2a (n : ℕ → ℕ) (hn : ∀ i, n i ≤ 2) (hsum : ∑ i ∈ Finset.range 16, n i = 16) (hne : ∃ i < 16, n i ≠ 1)
    (hab : (n 0 = 0 ∧ n 1 = 1 ∧ n 2 = 0) ∨ (n 0 = 0 ∧ n 1 = 1 ∧ n 2 = 2)) :
    ∃ e s tx ty, Sixteen.Matches Sixteen.sixteenLib n e s tx ty := by sorry
