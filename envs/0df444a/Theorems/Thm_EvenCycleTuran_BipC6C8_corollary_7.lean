-- Prove2me | Theorems.Thm_EvenCycleTuran_BipC6C8_corollary_7
-- name    : EvenCycleTuran.BipC6C8.corollary_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:32.110848+00:00
-- url     : https://prove2.me/theorems/d78c9a82-75ea-482a-896d-e0bdd95b7a5d
-- title:
--   Corollary 7, p. 4 — a Berge-C₄-free hypergraph on n vertices has Σ|e| = O(n^{1.5})
-- statement:
--   There is an absolute constant $C$ such that for every $n$ and every Berge-$C_4$-free hypergraph $\mathcal H$ on $n$ vertices,
--   $$\sum_{e\in E(\mathcal H)}|e|\le C\,n^{3/2}.$$
--
--   The paper derives this from the Győri–Lemons theorems on Berge cycles (Theorems 5 and 6). It is applied to the hypergraph $\mathcal H$ of Claim 7.
--
--   **Formalization Note** A hypergraph on $n$ vertices is a finite set of subsets of $\{0,\dots,n-1\}$ (distinct hyperedges, of arbitrary sizes). The constant is chosen before $n$ and $\mathcal H$.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 4, Corollary 7 (from Győri–Lemons, Theorems 5 and 6, pp. 3–4)

import Mathlib
import Definitions.Def_EvenCycleTuran_BipC6C8_Setting
open Finset SimpleGraph Filter Asymptotics

namespace EvenCycleTuran.BipC6C8

theorem corollary_7 :
    ∃ C : ℝ, ∀ (n : ℕ) (H : Finset (Finset (Fin n))), BergeC4Free H →
      (∑ e ∈ H, (e.card : ℝ)) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2) := by sorry

end EvenCycleTuran.BipC6C8
