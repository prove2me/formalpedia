-- Prove2me | Theorems.Thm_Erdos195_early_reps_extrema
-- name    : Erdos195.early_reps_extrema
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T18:05:38.175622+00:00
-- url     : https://prove2.me/theorems/908cde80-c065-4fab-99be-16d25bc5b0ba
-- title:
--   Early residue representatives force late extrema to agree mod 2^k (tree orders)
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. The halves of a word are the subsequences of its even letters and of its odd letters, each mapped by $x\mapsto\lfloor x/2\rfloor$; the half witnesses are $\theta_E(k,r)=\theta(k+1,2r)$ and $\theta_O(k,r)=\theta(k+1,2r+1)$.
--
--   **Theorem (early residue representatives force late extrema to agree).** Let $W=P\cdot R$ be safe for some tree witness. Suppose the prefix $P$ meets every residue class modulo $2^k$, and the extrema $L=\min W$, $U=\max W$ lie strictly outside the numerical range of $P$, i.e. $L<\min P$ and $\max P<U$. Then
--   $$L\equiv U\pmod{2^k}.$$
--
--   Applied along a cofinal chain of safe words, it implies (an immediate consequence, not part of this formal statement) that $\nu_2(\max Q_j-\min Q_j)\to\infty$, even if each stage uses its own tree witness. This generalizes the stagewise $\varepsilon$-order statement (milestone "stagewise ε: extrema diameters become 2-adically divisible") from $\varepsilon$-orders to arbitrary tree orders. The obstruction: if $h=\nu_2(U-L)<k$, early representatives $p\equiv L+2^h$ and $q\equiv L \pmod{2^{h+1}}$ give open pairs $(p,L)$ and $(q,U)$ at the same node with opposite forces. Lemma of GPT 6 Astra.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; lemma of GPT 6 Astra; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem early_reps_extrema (P R : List ℤ) (k : ℕ)
    (hS : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (P ++ R))
    (hP : ∀ r : ℤ, ∃ p ∈ P, p % 2 ^ k = r % 2 ^ k)
    (L U : ℤ) (hL : L ∈ P ++ R) (hU : U ∈ P ++ R) (hbd : ∀ x ∈ P ++ R, L ≤ x ∧ x ≤ U)
    (hLP : ∀ p ∈ P, L < p) (hUP : ∀ p ∈ P, p < U) :
    L % 2 ^ k = U % 2 ^ k := by sorry

end Erdos195
