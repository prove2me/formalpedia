-- Prove2me | Theorems.Thm_CyclicGroups_card_pow_eq_le_gcd
-- name    : CyclicGroups.card_pow_eq_le_gcd
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T12:53:41.623605+00:00
-- url     : https://prove2.me/theorems/900734e6-7c24-47ef-9926-7b1985c48495
-- title:
--   The number of $k$-th roots in a finite cyclic group
-- statement:
--   **The number of $k$-th roots of an element in a finite cyclic group.**
--
--   Let $G$ be a finite cyclic group of order $n$ and let $a \in G$. Then the equation $x^k = a$ has
--   at most $\gcd(k,n)$ solutions:
--
--   $$\#\{x \in G : x^{k} = a\} \;\le\; \gcd(k, n).$$
--
--   The bound is sharp and the behaviour is all-or-nothing: the map $x \mapsto x^{k}$ is a group
--   homomorphism whose kernel is the set of $k$-th roots of unity, which in a cyclic group of order
--   $n$ has size exactly $\gcd(k,n)$. Consequently every fibre of $x \mapsto x^k$ is either **empty**
--   (when $a$ is not a $k$-th power) or a coset of that kernel, hence of size exactly $\gcd(k,n)$.
--
--   Taking $a = 1$ recovers the familiar statement that a cyclic group of order $n$ contains exactly
--   $\gcd(k,n)$ elements of order dividing $k$ — equivalently, that $x^k = 1$ has exactly
--   $\gcd(k,n)$ solutions, the cyclic-group counterpart of the fact that a polynomial of degree $k$
--   over a field has at most $k$ roots.
--
--   Counts of this kind are the standard input when evaluating character sums or counting solutions
--   of $x^k = a$ in $(\mathbb{Z}/p)^\times$, which is cyclic of order $p-1$; there the bound reads
--   $\gcd(k, p-1)$ and underlies the theory of $k$-th power residues.
--
--   **Formalization note.** The solution set is written as a `Finset.filter` over `Finset.univ`, so
--   its `card` is the number of solutions; `IsCyclic G` is Mathlib's cyclicity hypothesis.
-- source:
--   Classical; see Lang, *Algebra*, Ch. I, and Ireland & Rosen, *A Classical Introduction to Modern Number Theory*, §4.1. Lean proof extracted from `Salt/Maynard/PpRootCyc.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace CyclicGroups

theorem card_pow_eq_le_gcd {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [IsCyclic G]
    (k : ℕ) (a : G) :
    (Finset.univ.filter (fun x : G => x ^ k = a)).card ≤ Nat.gcd k (Fintype.card G) := by sorry

end CyclicGroups
