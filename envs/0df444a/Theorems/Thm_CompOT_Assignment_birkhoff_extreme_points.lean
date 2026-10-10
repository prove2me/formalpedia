-- Prove2me | Theorems.Thm_CompOT_Assignment_birkhoff_extreme_points
-- name    : CompOT.Assignment.birkhoff_extreme_points
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T00:25:23.372664+00:00
-- url     : https://prove2.me/theorems/38d9cb6e-c607-4118-9763-0088040603de
-- title:
--   Proof of Proposition 2.1, p. 373 — Birkhoff extreme points in the book's scaling
-- statement:
--   Let $n>0$ and let $u$ be the uniform histogram with mass $1/n$ at each index. The extreme points of the coupling polytope $U(u,u)$ are exactly the scaled permutation matrices:
--
--   $$\operatorname{Ext}(U(u,u))=\{P_\sigma:\sigma\in\operatorname{Perm}(n)\}. $$
--
--   This specializes Birkhoff's theorem to the normalization used for probability histograms in the matching proposition.
--
--   **Formalization Note** Mathlib's doubly stochastic matrices have row and column sums $1$; the statement here uses the book's row and column sums $1/n$.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), proof of Proposition 2.1, p. 373, first sentence

import Mathlib
import Definitions.Def_CompOT_Assignment_Defs

namespace CompOT.Assignment

theorem birkhoff_extreme_points {n : ℕ} (hn : 0 < n) :
    Set.extremePoints ℝ (couplings (uniform n) (uniform n)) =
      {P : Matrix (Fin n) (Fin n) ℝ | ∃ σ : Equiv.Perm (Fin n), P = permCoupling σ} := by sorry

end CompOT.Assignment
