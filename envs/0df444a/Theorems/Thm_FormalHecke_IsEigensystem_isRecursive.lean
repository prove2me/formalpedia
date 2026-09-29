-- Prove2me | Theorems.Thm_FormalHecke_IsEigensystem_isRecursive
-- name    : FormalHecke.IsEigensystem.isRecursive
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/988bdb47-b323-5d63-813a-d9fae8c0f235
-- title:
--   Formal Hecke eigensystems satisfy the Hecke recursions
-- statement:
--   Let $R$ be a commutative ring and let $e, a : \mathbb{N} \to R$ be two sequences in $R$. Assume the pair $(e,a)$ is a formal Hecke eigensystem, i.e. $a(1) = 1$ and for every prime $\ell$ and every natural number $n$ one has $a(\ell n) + e(\ell)\cdot\bigl(a(n/\ell) \text{ if } \ell \mid n,\ 0 \text{ otherwise}\bigr) = a(\ell)\,a(n)$, where $n/\ell$ is natural-number division. The conclusion is that $(e,a)$ is recursive in the sense of the project's predicate `IsRecursive`, namely the conjunction of three assertions: $a(1) = 1$; for all natural numbers $m, n$ with $m$ and $n$ coprime, $a(mn) = a(m)\,a(n)$; and for every prime $\ell$ and every $r \in \mathbb{N}$, $a(\ell^{r+2}) = a(\ell)\,a(\ell^{r+1}) - e(\ell)\,a(\ell^{r})$. Thus the single eigenvector identity indexed by primes is shown to be equivalent in strength to (in particular, to imply) multiplicativity over coprime indices together with the three-term recursion at each prime power.
--
--   This is the passage from the Hecke eigenvector relations to the classical multiplicativity and prime-power recursion for the coefficients of an eigenform, i.e. the step that lets one factor the Dirichlet series of an eigensystem into Euler factors. It is used in the Deligne–Serre part of the development, in the identification of the Euler factors and tame level of a weight-one newform whose $q$-expansion coefficients are given by traces of Frobenius.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalHecke_IsEigensystem_isRecursive.lean

import Mathlib
import Definitions.Def_FormalHecke_Eigensystem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open FormalHecke

theorem FormalHecke.IsEigensystem.isRecursive {R : Type*} [CommRing R] {e a : ℕ → R}
    (h : FormalHecke.IsEigensystem e a) : FormalHecke.IsRecursive e a := by sorry
