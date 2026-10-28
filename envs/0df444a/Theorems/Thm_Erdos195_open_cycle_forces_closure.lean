-- Prove2me | Theorems.Thm_Erdos195_open_cycle_forces_closure
-- name    : Erdos195.open_cycle_forces_closure
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T21:52:06.911421+00:00
-- url     : https://prove2.me/theorems/515bf506-185a-48a4-a506-624143a99f96
-- title:
--   Open cycles force closures at their nodes, for every tree witness
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$ (milestone framework). A finite word $Q$ of integers is $\theta$-safe if the sequence "letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression; positions are first occurrences. For an in-order pair $(a,b)$ of a word ($a$ before $b$), call $2b-a$ its third term and $3b-2a$ its fourth term; the pair is closed if one of them occurs. An open cycle in a word $T$ is a family of in-order pairs $(a_i,b_i)$, $0\le i<m$, of letters of $T$ with
--   $$3b_i-2a_i \;=\; 2b_{i+1}-a_{i+1}\qquad(\text{indices mod } m)$$
--   and no third term $2b_i-a_i$ in $T$. Write $k_i=\nu_2(b_i-a_i)$ for the 2-adic level of pair $i$; its node is the residue $a_i \bmod 2^{k_i}$. **Theorem (open cycles force closures at their nodes).** Let $(a_i,b_i)_{i<m}$ be an open cycle in $T$, fix $i<m$ and put $k=k_i$. Let $\theta$ be any tree witness and $R$ any word with $T\,R$ $\theta$-safe. If $x$ comes before $y$ in $T\,R$, with
--   $$\nu_2(y-x)=k,\qquad x\equiv a_i \pmod{2^k},\qquad y\not\equiv b_i \pmod{2^{k+1}},$$
--   then $2y-x$ or $3y-2x$ occurs in $T\,R$.
--
--   Every pair of an open cycle stays open forever (the open-cycles-never-close milestone), so it fixes the witness bit at its node for every safe extension. This theorem turns that into $\theta$-independent forcing: every pair at the same node with the opposite orientation must be closed, whatever witness is used. It is a structural lemma in the tree-witness approach to Erdős #195, not a construction or an impossibility result.
--
--   Formalization note: words are `List ℤ`, positions via `List.idxOf`, the pairs are `a b : ℕ → ℤ` on indices `i < m`, the successor index is `(i+1) % m`, and safety is `Safe (treeLt θ)`; the level is `padicValInt 2 (b i - a i)` and the congruences are stated as divisibility by powers of 2.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem open_cycle_forces_closure (θ : ℕ → ℤ → Bool) (T R : List ℤ) (m : ℕ) (a b : ℕ → ℤ)
    (ha : ∀ i < m, a i ∈ T) (hb : ∀ i < m, b i ∈ T)
    (hi : ∀ i < m, T.idxOf (a i) < T.idxOf (b i))
    (hcyc : ∀ i < m, 3 * b i - 2 * a i = 2 * b ((i + 1) % m) - a ((i + 1) % m))
    (ht : ∀ i < m, 2 * b i - a i ∉ T) (hS : Safe (treeLt θ) (T ++ R))
    (i : ℕ) (him : i < m) (x y : ℤ) (hx : x ∈ T ++ R) (hy : y ∈ T ++ R)
    (hxy : (T ++ R).idxOf x < (T ++ R).idxOf y)
    (hk : padicValInt 2 (y - x) = padicValInt 2 (b i - a i))
    (hnode : (2 : ℤ) ^ padicValInt 2 (b i - a i) ∣ x - a i)
    (hbit : ¬ (2 : ℤ) ^ (padicValInt 2 (b i - a i) + 1) ∣ y - b i) :
    2 * y - x ∈ T ++ R ∨ 3 * y - 2 * x ∈ T ++ R := by sorry

end Erdos195
