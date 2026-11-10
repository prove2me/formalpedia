-- Prove2me | Theorems.Thm_FatFlat_Hereditary_theorem_2_1
-- name    : FatFlat.Hereditary.theorem_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:44:15.182619+00:00
-- url     : https://prove2.me/theorems/a7838eb8-6f25-4dc2-9b96-99cc79e80ace
-- title:
--   Theorem 2.1 — many edges force $K_h$ as a 1-shallow minor (Alon–Krivelevich–Sudakov)
-- statement:
--   For all positive integers $h,n$: every graph $G$ with $n$ vertices and more than $\binom{h+1}{2}\,n^{3/2}$ edges contains the complete graph $K_h$ as a 1-shallow minor (a minor model whose branch sets induce subgraphs of radius at most 1). Here $n^{3/2}$ is the real power and the number of edges is $|E(G)|$.
--
--   This is a cited result ([5, Theorem 2.2] of Alon, Krivelevich and Sudakov, in the formulation of [31, Corollary 2.3]).
--
--   Differences from the source:
--   - encoding: an n-vertex graph → a simple graph on a finite vertex type V with Fintype.card V = n; reason: every n-vertex graph is such a graph and conversely
--   - encoding: number of edges, n^{3/2} → (G.edgeSet.ncard : ℝ) and (n : ℝ) ^ ((3 : ℝ) / 2); reason: the comparison is made in ℝ, where n^{3/2} is the usual real power
-- source:
--   Filtser, Le, Mählmann, Ma. Pilipczuk, Mi. Pilipczuk, Fatness and Flatness, arXiv:2607.21474, Theorem 2.1, p. 7 (PDF p. 9). Verbatim: 'Theorem 2.1. For all positive integers h, n, every n-vertex graph with more than (h+1 choose 2) n^{3/2} edges contains K_h as a 1-shallow minor.' PDF SHA-256: 757d7502abd8762f687daa2125d7908bd129bcf2f5d6d5cc1756b514302adaf1.

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Patterns
import Definitions.Def_FatFlat_Hereditary_Classes

set_option autoImplicit false

namespace FatFlat.Hereditary

/-- **Theorem 2.1** (Filtser et al., arXiv:2607.21474, p. 7; Alon–Krivelevich–Sudakov via
Pilipczuk–Siebertz–Toruńczyk, Cor. 2.3). For all positive integers `h, n`, every `n`-vertex
graph with more than `C(h+1, 2) · n^{3/2}` edges contains `K_h` as a 1-shallow minor. -/
theorem theorem_2_1 (h n : ℕ) (hh : 0 < h) (hn : 0 < n) (V : Type) [Fintype V]
    (hV : Fintype.card V = n) (G : SimpleGraph V)
    (hE : ((h + 1).choose 2 : ℝ) * (n : ℝ) ^ ((3 : ℝ) / 2) < (G.edgeSet.ncard : ℝ)) :
    IsShallowMinor (⊤ : SimpleGraph (Fin h)) G 1 := by sorry

end FatFlat.Hereditary
