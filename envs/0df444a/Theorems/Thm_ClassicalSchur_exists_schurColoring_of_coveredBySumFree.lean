-- Prove2me | Theorems.Thm_ClassicalSchur_exists_schurColoring_of_coveredBySumFree
-- name    : ClassicalSchur.exists_schurColoring_of_coveredBySumFree
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-04T00:29:17.139472+00:00
-- url     : https://prove2.me/theorems/2a19fa1c-aed6-47f7-8337-204e6538dad0
-- title:
--   A cover of $[1, N]$ by $n \ge 1$ sumfree sets gives a Schur colouring of $[1, N]$ with $n$ colours
-- statement:
--   This is the second direction of the passage between Schur colourings and covers by sumfree sets.
--
--   Let $n \ge 1$ and $N$ be natural numbers. A set $S \subseteq \mathbb{N}$ is **sumfree** if $x + y \notin S$ for all $x, y \in S$, the case $x = y$ included. Suppose that $[1, N]$ is covered by $n$ sumfree sets, that is, $[1, N] \subseteq C_0 \cup \dots \cup C_{n-1}$ for some sumfree sets $C_0, \dots, C_{n-1} \subseteq \mathbb{N}$. Then there is a colouring with $n$ colours that is a Schur colouring of $[1, N]$:
--
--   $$
--   \exists\, c : \mathbb{N} \to \mathrm{Fin}\,n \ \text{ such that there are no } x, y \ge 1 \text{ with } x + y \le N \text{ and } c(x) = c(y) = c(x + y).
--   $$
--
--   With `ClassicalSchur.coveredBySumFree_of_schurColoring`, for $n \ge 1$ a Schur colouring of $[1, N]$ with $n$ colours gives a cover of $[1, N]$ by $n$ sumfree sets, and such a cover gives a Schur colouring. So the Schur number $S(n)$, the largest $N$ for which $[1, N]$ has a Schur colouring with $n$ colours, is also the largest $N$ for which $[1, N]$ is covered by $n$ sumfree sets.
--
--   **Formalization Note.** The hypothesis is `CoveredBySumFree (Set.Icc 1 N) n`: the $n$ sets are indexed by `Fin n`, need not be disjoint and need not lie in $[1, N]$. The hypothesis $n \ge 1$ cannot be dropped: for $n = 0$ and $N = 0$ the empty interval is covered by no sets, but there is no function $\mathbb{N} \to \mathrm{Fin}\,0$. The colouring is a function on all of $\mathbb{N}$; the statement says nothing about its values outside $[1, N]$.
-- source:
--   A. McKenna, "S(6) ≤ 1801 if R₄(3) ≤ 61: a centred Schur bound and the structure at the frontier", Zenodo (2026), https://doi.org/10.5281/zenodo.23156099, Lemma 2.1 (b) (for n ≥ 1, a cover of [1, N] by n sumfree sets gives a Schur colouring with n colours). Lean source: https://github.com/mysticflounder/schur-centred-bound/blob/v1.0.1/ClassicalSchur/Frontier.lean#L75-L93 (release v1.0.1, doi:10.5281/zenodo.23156444).

import Definitions.Def_ClassicalSchurBasic
import Definitions.Def_ClassicalSchurColoring
import Mathlib

open ClassicalSchur
open Finset

theorem ClassicalSchur.exists_schurColoring_of_coveredBySumFree {n N : ℕ} (hn : 0 < n)
    (h : CoveredBySumFree (Set.Icc 1 N) n) : ∃ c : ℕ → Fin n, SchurColoring N c := by sorry
