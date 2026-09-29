-- Prove2me | Theorems.Thm_AKSSorting_Core_chainW_exists
-- name    : AKSSorting.Core.chainW_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T10:13:12.323821+00:00
-- url     : https://prove2.me/theorems/97bcb46e-15d5-4012-acd9-827a122bd2b8
-- title:
--   Lemma 2 — chains W(C, k) of prescribed sizes a_k − 1 ≤ N ≤ a_k
-- statement:
--   Let $C$ be a chain on level $i$ and let $a_0,\dots,a_{i-1}$ be nonnegative integers such that
--
--   - (2a) $\displaystyle 2\sum_{k<i}a_k<N(C)$, and
--   - (2.b) for every $s<i$: if $a_{s'}>0$ for some $s'<s$, then $\sum_{k<s}a_k<a_s$.
--
--   Then there are chains $W(C,k)$ on level $k$, $0\le k<i$, such that
--
--   1. (1.2) $(\cup W(C,k))\cap(\cup W(C,k'))=\emptyset$ for $k\ne k'$;
--   2. (1.4) with $j=0$: $W(C,k)(t')\subseteq\bigcup_{l(t)=i,\ t\prec t'}C(t)$ for every node $t'$ of level $k<i$;
--   3. (2.3) $a_k-1\le N(W(C,k))\le a_k$ for all $k<i$;
--   4. (2.5) the function $\overline W(t)=C(t)\setminus\bigcup_{k<i}(\cup W(C,k))$ on level $i$ is a chain and
--   $$ N(C)-\sum_{k<i}a_k\le N(\overline W)\le N(C). $$
--
--   It lets the algorithm move a prescribed number of registers, up to one, from the leaves to every higher level, keeping all levels chains.
--
--   **Formalization Note** "For all $k$ there exists a chain $W(C,k)$" is read as one family $W$ that satisfies all conditions jointly, since (1.2) relates different $k$. The quantifiers of (2.b) are read as displayed above. (1.1) is carried by the type (`W k` is a function on `Fin (2^k)`); (1.4) is required for levels $k<i$, the ones on which $W$ is defined. Inequality (2.3) and the lower bound of (2.5) are stated in $\mathbb Z$, since $a_k-1$ can be $-1$. The paper's numbering skips (2.4).
-- source:
--   Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983), p. 4, Lemma 2

import Mathlib
import Definitions.Def_AKSSorting_Core_IsChain

namespace AKSSorting.Core

/-- Lemma 2 (Ajtai–Komlós–Szemerédi 1983, p. 4). Let `C` be a chain on level `i` and
`a₀, …, a_{i-1}` nonnegative integers with
(2a) `2 ∑_{k<i} a_k < N(C)` and
(2.b) for every `s < i`, if `a_{s'} > 0` for some `s' < s`, then `∑_{k<s} a_k < a_s`.
Then there are chains `W(C, k)` on level `k`, `0 ≤ k < i`, such that (1.2) and (1.4) hold with
`j = 0` and `V = W` ((1.1) is carried by the type), and
(2.3) `a_k − 1 ≤ N(W(C, k)) ≤ a_k` for all `k < i`;
(2.5) `W̄(t) = C(t) − ⋃_{k<i} ∪W(C, k)` is a chain with `N(C) − ∑_{k<i} a_k ≤ N(W̄) ≤ N(C)`. -/
theorem chainW_exists {R : Type} [DecidableEq R] {i : ℕ} (C : Fin (2 ^ i) → Finset R)
    (hC : IsChain C) (a : ℕ → ℕ)
    (h2a : 2 * ∑ k ∈ Finset.range i, a k < chainN C)
    (h2b : ∀ s < i, (∃ s' < s, 0 < a s') → ∑ k ∈ Finset.range s, a k < a s) :
    ∃ W : (k : ℕ) → Fin (2 ^ k) → Finset R,
      (∀ k < i, IsChain (W k)) ∧
      (∀ k < i, ∀ k' < i, k ≠ k' → Disjoint (chainUnion (W k)) (chainUnion (W k'))) ∧
      (∀ k < i, ∀ t' : Fin (2 ^ k), W k t' ⊆ subtreeUnion C k t') ∧
      (∀ k < i, (a k : ℤ) - 1 ≤ (chainN (W k) : ℤ) ∧ chainN (W k) ≤ a k) ∧
      (IsChain (fun t => C t \ (Finset.range i).biUnion fun k => chainUnion (W k)) ∧
        (chainN C : ℤ) - ∑ k ∈ Finset.range i, (a k : ℤ) ≤
          (chainN (fun t => C t \ (Finset.range i).biUnion fun k => chainUnion (W k)) : ℤ) ∧
        chainN (fun t => C t \ (Finset.range i).biUnion fun k => chainUnion (W k)) ≤
          chainN C) := by sorry

end AKSSorting.Core
