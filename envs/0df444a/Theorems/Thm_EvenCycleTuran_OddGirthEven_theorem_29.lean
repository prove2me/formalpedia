-- Prove2me | Theorems.Thm_EvenCycleTuran_OddGirthEven_theorem_29
-- name    : EvenCycleTuran.OddGirthEven.theorem_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:02.571477+00:00
-- url     : https://prove2.me/theorems/f6925b46-9ab1-4212-ae51-e34ae33ace67
-- title:
--   Theorem 29 — many edges in a uniform hypergraph of prescribed Berge girth
-- statement:
--   Let $r\ge2$ and $s\ge3$ be integers. For all sufficiently large $n$, there is an $r$-uniform hypergraph $\mathcal H$ on $n$ vertices with Berge girth at least $s$ and
--
--   $$|E(\mathcal H)|\ge n^{1+1/s}.$$
--
--   This cited result of Nešetřil and Rödl supplies the hypergraphs used in the lower bound for Theorem 17. The threshold on $n$ may depend on $r$ and $s$.
--
--   **Formalization Note** Hyperedges are distinct finite vertex sets; Berge cycles require distinct vertices and distinct hyperedges. Girth at least $s$ means absence of every Berge cycle of length $2,\ldots,s-1$.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 27, Theorem 29 (citing Nešetřil–Rödl [32])

import Mathlib
import Definitions.Def_EvenCycleTuran_OddGirthEven_Setting

namespace EvenCycleTuran.OddGirthEven

/-- Theorem 29 (Nešetřil–Rödl), p. 27. -/
theorem theorem_29 (r s : ℕ) (hr : 2 ≤ r) (hs : 3 ≤ s) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ H : Hypergraph (Fin n),
        IsUniform H r ∧ GirthGe H s ∧
          (n : ℝ) ^ ((1 : ℝ) + 1 / (s : ℝ)) ≤ (H.card : ℝ) := by sorry

end EvenCycleTuran.OddGirthEven
