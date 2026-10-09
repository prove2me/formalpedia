-- Prove2me | Theorems.Thm_EvenCycleTuran_OddGirthOdd_theorem_29
-- name    : EvenCycleTuran.OddGirthOdd.theorem_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:25:14.719261+00:00
-- url     : https://prove2.me/theorems/c21f79e8-a2f9-4cb6-898e-391f7ef65368
-- title:
--   Theorem 29 (Nešetřil–Rödl) — r-uniform hypergraphs of girth ≥ s with at least n^{1+1/s} edges
-- statement:
--   Let $r \ge 2$ and $s \ge 3$ be integers. Then there is an integer $n_0$ such that for every $n \ge n_0$ there is an $r$-uniform hypergraph $\mathcal H$ on $n$ vertices of girth at least $s$ (no Berge cycle of length $2, \dots, s-1$) with
--
--   $$|E(\mathcal H)| \ge n^{1 + 1/s}.$$
--
--   This classical result of Nešetřil and Rödl, cited in the paper, supplies the sparse high-girth hypergraphs from which the lower-bound graphs of Theorems 17 and 18 are built.
--
--   **Formalization Note** The hypergraph lives on the vertex set `Fin n`; isolated vertices are allowed. The exponent $1 + 1/s$ is a real power.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 27, Theorem 29 (citing Nešetřil and Rödl [32])

import Mathlib
import Definitions.Def_EvenCycleTuran_OddGirthOdd_Setting

namespace EvenCycleTuran.OddGirthOdd

/-- Theorem 29 (Nešetřil–Rödl), p. 27. -/
theorem theorem_29 (r s : ℕ) (hr : 2 ≤ r) (hs : 3 ≤ s) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ H : Hypergraph (Fin n),
        IsUniform H r ∧ GirthGe H s ∧
          (n : ℝ) ^ ((1 : ℝ) + 1 / (s : ℝ)) ≤ (H.card : ℝ) := by sorry

end EvenCycleTuran.OddGirthOdd
