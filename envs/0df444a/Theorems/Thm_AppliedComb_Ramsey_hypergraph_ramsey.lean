-- Prove2me | Theorems.Thm_AppliedComb_Ramsey_hypergraph_ramsey
-- name    : AppliedComb.Ramsey.hypergraph_ramsey
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:29:01.604122+00:00
-- url     : https://prove2.me/theorems/6a832b42-1a0c-4b35-a0ec-d39212aa1084
-- title:
--   Theorem 11.6 — Ramsey's Theorem for s-subsets and r colours
-- statement:
--   Let $r$ and $s$ be positive integers and let $h = (h_1, h_2, \dots, h_r)$ be a string of integers with $h_i \ge s$ for each $i = 1, 2, \dots, r$. Then there exists a least positive integer $R(s : h_1, h_2, \dots, h_r)$ such that, whenever $n \ge R(s : h_1, \dots, h_r)$ and
--   $$\phi : C([n], s) \longrightarrow [r]$$
--   is any function, there exist a colour $\alpha \in [r]$ and a subset $H_\alpha \subseteq [n]$ with $|H_\alpha| = h_\alpha$ such that $\phi(S) = \alpha$ for every $S \in C(H_\alpha, s)$.
--
--   Here $[n] = \{1, \dots, n\}$ and $C(X, s)$ is the family of $s$-element subsets of $X$. The case $s = 1$ is the Pigeon Hole Principle and the case $s = r = 2$ is Ramsey's Theorem for Graphs (Theorem 11.2). The book states this theorem without proof.
--
--   **Formalization Note.** The printed statement has three typos, read as follows: the hypothesis "$h_i \ge s$ for each $i = 1, 2, \dots, s$" is read with $i$ ranging over $1, \dots, r$ (the string has $r$ entries); the threshold "$n \ge n_0$", where $n_0$ is never introduced, is read as $n \ge R(s : h_1, \dots, h_r)$; and "$C([n], s]$" is $C([n], s)$. The statement is `IsLeast {N | 0 < N ∧ IsHypergraphRamseyBound s r h N} (hypergraphRamseyNumber s r h)` with `h : Fin r → ℕ`; ground set `Fin n`, colours `Fin r`, both 0-based.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 234, Theorem 11.6 (stated without proof; typos read as in the Formalization Note)

import Mathlib
import Definitions.Def_AppliedComb_Ramsey_hypergraphRamseyNumber

namespace AppliedComb.Ramsey

/-- Theorem 11.6 (Ramsey's Theorem), Keller & Trotter p. 234, with the page's typos read as
follows: the hypothesis `h_i ≥ s` ranges over `i = 1, …, r` (the page prints `i = 1, …, s`), the
undefined threshold `n_0` is `R(s : h_1, …, h_r)` itself, and `C([n], s]` is `C([n], s)`. For
positive integers `r, s` and `h = (h_1, …, h_r)` with every `h_i ≥ s`, there is a least positive
integer `R(s : h_1, …, h_r)` such that for every `n ≥ R(s : h)` every colouring of the
`s`-subsets of `[n]` with `r` colours has, for some colour `α`, a set of `h_α` points all of whose
`s`-subsets have colour `α`; `hypergraphRamseyNumber s r h` is it. -/
theorem hypergraph_ramsey (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (h : Fin r → ℕ)
    (hh : ∀ i, s ≤ h i) :
    IsLeast {N : ℕ | 0 < N ∧ IsHypergraphRamseyBound s r h N}
      (hypergraphRamseyNumber s r h) := by sorry

end AppliedComb.Ramsey
