-- Prove2me | Theorems.Thm_CircletTSP_Facet_stsp_vectorSpan_eq_degree_zero
-- name    : CircletTSP.Facet.stsp_vectorSpan_eq_degree_zero
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-22T18:01:29.125873+00:00
-- url     : https://prove2.me/theorems/0fbd125a-15ca-4142-a40c-1639632e1590
-- title:
--   Affine directions of the symmetric TSP polytope are exactly zero-degree symmetric arrays
-- statement:
--   For $n\ge3$, the space of affine directions of the symmetric traveling-salesman polytope consists exactly of real arrays $x=(x_{ij})$ which are symmetric, vanish on the diagonal, and satisfy $\sum_j x_{ij}=0$ for every vertex $i$. Tours are represented in the unchanged ordered-pair incidence coordinates. The forward inclusion expresses that every tour has degree two. The reverse inclusion is the substantive tour-exchange spanning assertion. This structural lemma supports the existing public `CircletTSP.Facet.stsp_dim` milestone; it does not assert a dimension formula or assume the desired dimension. The boundary case $n=3$ has zero direction space.
-- source:
--   Research-derived structural affine-hull lemma for the STSP dimension statement cited by Gutekunst–Williamson, The Circlet Inequalities, arXiv:2012.12363v1, p.19 (citing Naddef–Rinaldi, Theorem3.7). This characterization is an auxiliary research goal, not a verbatim theorem claimed in that paper.

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection
import Definitions.Def_CircletTSP_Facet_Setting

namespace CircletTSP.Facet

theorem stsp_vectorSpan_eq_degree_zero (n : ℕ) (hn : 3 ≤ n) :
    (vectorSpan ℝ (STSP n) : Set (Fin n → Fin n → ℝ)) =
      {x | (∀ i j, x i j = x j i) ∧ (∀ i, x i i = 0) ∧ ∀ i, ∑ j, x i j = 0} := by sorry

end CircletTSP.Facet
