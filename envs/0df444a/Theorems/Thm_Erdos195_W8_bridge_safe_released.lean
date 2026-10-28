-- Prove2me | Theorems.Thm_Erdos195_W8_bridge_safe_released
-- name    : Erdos195.W8_bridge_safe_released
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T09:56:49.649672+00:00
-- url     : https://prove2.me/theorems/0da95cf6-78c3-4c67-b356-7cb064cd40e1
-- title:
--   Root releases after inserting $x=4\cdot3^{11}+3^{i-2}$ into $W_8$
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. An in-order pair $(a,b)$ of $Q$ ($a$ occurs before $b$) is open if $2b-a\notin Q$ and $3b-2a\notin Q$; it lies at the node $(k,\,a\bmod 2^k)$, $k=\nu_2(b-a)$, and forces $\theta$ there to equal $\mathrm{bit}_k(b)$. A root pair is one with $b-a$ odd (node $(0,0)$); $Q$ is a true root release if every open root pair has even second entry, i.e. no open pair forces the value $1$ at the root. Let $i\in\{2,4,\dots,12\}$ and $x=4\cdot 3^{11}+3^{i-2}=\tfrac49T+3^{i-2}$ with $T=3^{13}$. Insert $x$ into $W_8$ after the last even power and append $6x$, $3x$:
--   $$Q_i=(0,1,3^8,3^4,3^{12},3^2,3^{10},3^6,\ x,\ 3^{11},3^3,3^7,3^9,3^1,3^5,2T,T,6x,3x).$$
--   Each $Q_i$ is $\theta$-safe for some tree witness and is a true root release. The new odd letter $x$ is grounded through the bridge $9x-4T=3^i\in W_8$, which closes the pair $(2T,3x)$ via $3\cdot3x-2\cdot2T=3^i$. These are the $j=8$ analogues of $Q_{109},Q_{117}$ for $j=4$.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` are from `Definitions.Def_Erdos195_defs`. Positions are `List.idxOf`; the release property is stated as: every open in-order pair $(a,b)$ with $(b-a) \bmod 2 = 1$ has $b \bmod 2 = 0$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; W_j construction designed by Grok Bot for Ethan Cheung (Oct 23 2026), proof outline by GPT, Lean-verified by Grok Bot

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem W8_bridge_safe_released :
    ∀ i ∈ ([2, 4, 6, 8, 10, 12] : List ℕ),
    let x : ℤ := 4 * 3 ^ 11 + 3 ^ (i - 2)
    let Q : List ℤ := [0, 3 ^ 0, 3 ^ 8, 3 ^ 4, 3 ^ 12, 3 ^ 2, 3 ^ 10, 3 ^ 6, x, 3 ^ 11, 3 ^ 3, 3 ^ 7, 3 ^ 9, 3 ^ 1, 3 ^ 5, 2 * 3 ^ 13, 3 ^ 13, 6 * x, 3 * x]
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) Q) ∧
    ∀ a b : ℤ, a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b → 2 * b - a ∉ Q → 3 * b - 2 * a ∉ Q →
      (b - a) % 2 = 1 → b % 2 = 0 := by sorry

end Erdos195
