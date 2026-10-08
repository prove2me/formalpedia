-- Prove2me | Theorems.Thm_ClassicalSchur_coveredBySumFree_of_schurColoring
-- name    : ClassicalSchur.coveredBySumFree_of_schurColoring
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-04T00:27:08.807899+00:00
-- url     : https://prove2.me/theorems/d2d1b7c1-3669-448d-83c0-972befbc1198
-- title:
--   A Schur colouring of $[1, N]$ with $n$ colours gives a cover of $[1, N]$ by $n$ sumfree sets
-- statement:
--   This is one direction of the passage between Schur colourings and covers by sumfree sets.
--
--   Let $n, N \in \mathbb{N}$, and let $c : \mathbb{N} \to \mathrm{Fin}\,n$ be a colouring with $n$ colours that is a Schur colouring of $[1, N]$: there are no $x, y \ge 1$ with $x + y \le N$ and $c(x) = c(y) = c(x + y)$, the case $x = y$ included. A set $S \subseteq \mathbb{N}$ is **sumfree** if $x + y \notin S$ for all $x, y \in S$, again with $x = y$ allowed. Then $[1, N]$ is covered by $n$ sumfree sets:
--
--   $$
--   [1, N] \subseteq C_0 \cup C_1 \cup \dots \cup C_{n-1} \qquad \text{for some sumfree sets } C_0, \dots, C_{n-1} \subseteq \mathbb{N}.
--   $$
--
--   Together with the converse bridge `ClassicalSchur.exists_schurColoring_of_coveredBySumFree`, this lets the mission move between the colouring form `SchurColoring`, used by the frontier theorems, and the cover form `CoveredBySumFree`, used by the centred bound. For example, under $\mathrm{TR}(k, r)$ the centred bound excludes a cover of $[1, 2(k+1)\lfloor (r-1)/2 \rfloor + 2]$ by $k + 1$ sumfree sets, and through this theorem it excludes a Schur colouring of that interval with $k + 1$ colours.
--
--   **Formalization Note.** The conclusion is `CoveredBySumFree (Set.Icc 1 N) n`: there are $n$ sets of naturals, indexed by `Fin n`, each sumfree in $\mathbb{N}$, whose union contains $[1, N]$. The sets need not be disjoint and need not lie in $[1, N]$. The colouring is a function on all of $\mathbb{N}$, and only its values on $[1, N]$ are constrained. For $n = 0$ there is no function $\mathbb{N} \to \mathrm{Fin}\,0$, so the statement is vacuous there; for $N = 0$ the interval is empty.
-- source:
--   A. McKenna, "S(6) ≤ 1801 if R₄(3) ≤ 61: a centred Schur bound and the structure at the frontier", Zenodo (2026), https://doi.org/10.5281/zenodo.23156099, Lemma 2.1 (a) (a Schur colouring of [1, N] with n colours gives a cover of [1, N] by n sumfree sets). Lean source: https://github.com/mysticflounder/schur-centred-bound/blob/v1.0.1/ClassicalSchur/Frontier.lean#L64-L73 (release v1.0.1, doi:10.5281/zenodo.23156444).

import Definitions.Def_ClassicalSchurBasic
import Definitions.Def_ClassicalSchurColoring
import Mathlib

open ClassicalSchur
open Finset

theorem ClassicalSchur.coveredBySumFree_of_schurColoring {n N : ℕ} {c : ℕ → Fin n}
    (hc : SchurColoring N c) : CoveredBySumFree (Set.Icc 1 N) n := by sorry
