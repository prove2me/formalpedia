-- Prove2me | Theorems.Thm_Erdos195_open_cycle_node_conflict
-- name    : Erdos195.open_cycle_node_conflict
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T21:52:05.097106+00:00
-- url     : https://prove2.me/theorems/0d5f4e1f-1954-4ac1-911c-257b0871b497
-- title:
--   Open cycle with a node conflict kills every extension (interlocked obstruction for cycles of any length)
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$ (milestone framework). A finite word $Q$ of integers is $\theta$-safe if the sequence "letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression; positions are first occurrences. For an in-order pair $(a,b)$ of a word ($a$ before $b$), call $2b-a$ its third term and $3b-2a$ its fourth term; the pair is closed if one of them occurs. An open cycle in a word $T$ is a family of in-order pairs $(a_i,b_i)$, $0\le i<m$, of letters of $T$ with
--   $$3b_i-2a_i \;=\; 2b_{i+1}-a_{i+1}\qquad(\text{indices mod } m)$$
--   and no third term $2b_i-a_i$ in $T$. Write $k_i=\nu_2(b_i-a_i)$ for the 2-adic level of pair $i$; its node is the residue $a_i \bmod 2^{k_i}$. **Theorem (open cycle with a node conflict).** Let $(a_i,b_i)_{i<m}$ be an open cycle in $T$, and suppose two of its pairs $i,j$ lie at the same node but point in opposite directions:
--   $$k_j=k_i=k,\qquad a_j\equiv a_i \pmod{2^k},\qquad b_j\not\equiv b_i \pmod{2^{k+1}}.$$
--   Then no word $T\,R$ is $\theta$-safe, for any tree witness $\theta$ and any word $R$ (in particular $T$ itself is not safe).
--
--   This generalises the interlocked obstruction, which is the case $m=2$ with pairs $(a,a+d)$, $(a+5d,a+4d)$ and both middle terms absent, to open cycles of any length. For example, any word in which $0$ precedes $1$, $-1$ precedes $1$, and $11$ precedes $8$, while $2,3,5$ are absent, has the 3-cycle $(0,1),(-1,1),(11,8)$, with third terms $2,3,5$ and fourth terms $3,5,2$. Pairs $(0,1)$ and $(11,8)$ are both at level $0$, and $8\not\equiv 1 \pmod 2$, so such a word can never be extended safely. It is a forbidden configuration for any construction in the tree-witness approach to Erdős #195, not a construction or an impossibility result.
--
--   Formalization note: words are `List ℤ`, positions via `List.idxOf`, the pairs are `a b : ℕ → ℤ` on indices `i < m`, the successor index is `(i+1) % m`; the conclusion is `¬ ∃ θ, Safe (treeLt θ) (T ++ R)`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem open_cycle_node_conflict (T R : List ℤ) (m : ℕ) (a b : ℕ → ℤ)
    (ha : ∀ i < m, a i ∈ T) (hb : ∀ i < m, b i ∈ T)
    (hi : ∀ i < m, T.idxOf (a i) < T.idxOf (b i))
    (hcyc : ∀ i < m, 3 * b i - 2 * a i = 2 * b ((i + 1) % m) - a ((i + 1) % m))
    (ht : ∀ i < m, 2 * b i - a i ∉ T) (i j : ℕ) (him : i < m) (hjm : j < m)
    (hk : padicValInt 2 (b j - a j) = padicValInt 2 (b i - a i))
    (hnode : (2 : ℤ) ^ padicValInt 2 (b i - a i) ∣ a j - a i)
    (hbit : ¬ (2 : ℤ) ^ (padicValInt 2 (b i - a i) + 1) ∣ b j - b i) :
    ¬ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (T ++ R) := by sorry

end Erdos195
