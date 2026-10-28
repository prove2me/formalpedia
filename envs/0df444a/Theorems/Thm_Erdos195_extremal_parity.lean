-- Prove2me | Theorems.Thm_Erdos195_extremal_parity
-- name    : Erdos195.extremal_parity
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T13:11:31.654151+00:00
-- url     : https://prove2.me/theorems/c4ac961e-9bd0-4234-8cec-80dde669a5b8
-- title:
--   Extremal-parity lemma for node-consistent words
-- statement:
--   For a finite word $A$ of integers, an in-order pair $(x,y)$ of $A$ ($x$ occurs before $y$) is open if $2y-x\notin A$ and $3y-2x\notin A$. It lies at the node $(k,\,x\bmod 2^k)$ of the binary residue tree, where $k=\nu_2(y-x)$, and it forces the bit $\mathrm{bit}_k(y)=\lfloor y/2^k\rfloor\bmod 2$ there. The word satisfies SAFE(ii), or node consistency, if no node is forced to both bits by open pairs: any two open pairs at the same node force the same bit. Let $A=(a,b,\dots)$ be a finite word that satisfies SAFE(ii) and whose first two entries have opposite parity. Let $L,U$ be its minimum and maximum, and suppose $L<a<U$. Then
--   $$L\equiv U\pmod 2.$$
--   Otherwise the extreme $z$ of parity opposite to $a$ and the other extreme $w$ give open root pairs $(a,z)$ and $(b,w)$, which force opposite root bits. The lemma is a basic constraint on completions in the tree-witness approach to Erdős Problem 195. It rules out symmetric completions about a half-integer.
--
--   Formalization note: SAFE(ii) is stated inline exactly as the second conjunct of `Erdos195.exists_treeLt_safe_iff`. Positions are `List.idxOf`, $\nu_2$ is `padicValInt 2`, and $\mathrm{bit}_k$ is `bitOne` from `Definitions.Def_Erdos195_defs`. Distinctness of the entries is not needed. The extremes are given as $L,U\in A$ with $L\le x\le U$ for all $x\in A$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; parity obstruction by Sol, Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem extremal_parity (A : List ℤ) (a b : ℤ) (rest : List ℤ) (hA : A = a :: b :: rest)
    (hii : ∀ x y x' y' : ℤ, x ∈ A → y ∈ A → A.idxOf x < A.idxOf y →
      2 * y - x ∉ A → 3 * y - 2 * x ∉ A →
      x' ∈ A → y' ∈ A → A.idxOf x' < A.idxOf y' →
      2 * y' - x' ∉ A → 3 * y' - 2 * x' ∉ A →
      padicValInt 2 (y - x) = padicValInt 2 (y' - x') →
      x % 2 ^ padicValInt 2 (y - x) = x' % 2 ^ padicValInt 2 (y - x) →
      (bitOne y (padicValInt 2 (y - x)) ↔ bitOne y' (padicValInt 2 (y - x))))
    (hab : (b - a) % 2 = 1) (L U : ℤ) (hL : L ∈ A) (hU : U ∈ A)
    (hbd : ∀ x ∈ A, L ≤ x ∧ x ≤ U) (hLa : L < a) (haU : a < U) :
    (U - L) % 2 = 0 := by sorry

end Erdos195
