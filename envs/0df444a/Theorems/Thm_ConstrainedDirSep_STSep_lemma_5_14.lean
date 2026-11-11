-- Prove2me | Theorems.Thm_ConstrainedDirSep_STSep_lemma_5_14
-- name    : ConstrainedDirSep.STSep.lemma_5_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:05:39.849455+00:00
-- url     : https://prove2.me/theorems/1045c5cb-4a7e-45fe-8d69-90e06025448b
-- title:
--   Lemma 5.14 — a solvable instance has an inclusion-minimal solution
-- statement:
--   Let $\mathcal H$ be a hereditary class of digraphs (closed under isomorphism), $D$ a loopless digraph with distinct terminals $s,t$, and $k\ge0$. If the instance $(D,s,t,k)$ of H-Directed $s$–$t$ Separator has a solution, i.e. an $s$–$t$ vertex separator $S$ with $|S|\le k$ and $D[S]\in\mathcal H$, then it has a solution $S'$ that is an inclusion-minimal $s$–$t$ vertex separator.
--
--   This lets the algorithm of Theorem 1.1 search only among inclusion-minimal separators, which the representation theorem (Theorem 5.2) covers.
--
--   Differences from the source:
--   - generalization: H a class of loopless digraphs → any isomorphism-closed hereditary predicate on digraphs on {0, …, m−1} (it may also contain digraphs with loops); reason: only loopless digraphs ever occur (D is loopless), and every class of the source is such a predicate.
-- source:
--   Olkowski, Ramanujan, Constrained Directed Separation: Algorithms and Classifications, STOC 2027 submission (manuscript sha256 4dd06c29…), p. 25 (PDF 28), Lemma 5.14 (proof p. 44, PDF 47)

import Mathlib
import Definitions.Def_ConstrainedDirSep_STSep_Separator

namespace ConstrainedDirSep.STSep

/-- Olkowski, Ramanujan, *Constrained Directed Separation*, STOC 2027 submission (manuscript
sha256 4dd06c29…), p. 25 (PDF 28), Lemma 5.14: if `H` is hereditary and an instance of
H-Directed s–t Separator has a solution, then it has a solution which is inclusion-minimal as an
s–t separator. -/
theorem lemma_5_14 (H : DigraphClass) (hiso : IsoClosed H) (hher : Hereditary H)
    {n : ℕ} (D : Digraph (Fin n)) (hD : Loopless D) (s t : Fin n) (hst : s ≠ t) (k : ℕ)
    (S : Finset (Fin n)) (hS : IsFeasible H D s t k S) :
    ∃ S' : Finset (Fin n), IsFeasible H D s t k S' ∧ IsMinimalSTSeparator D s t (S' : Set (Fin n)) := by sorry

end ConstrainedDirSep.STSep
