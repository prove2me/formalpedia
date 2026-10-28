-- Prove2me | Theorems.Thm_Erdos195_W8_safe_released
-- name    : Erdos195.W8_safe_released
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T09:56:48.522999+00:00
-- url     : https://prove2.me/theorems/1ab9c1d0-6752-4f2a-b992-7e8a61fc2ed2
-- title:
--   The word $W_8$ is a tree-safe true root release
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. An in-order pair $(a,b)$ of $Q$ ($a$ occurs before $b$) is open if $2b-a\notin Q$ and $3b-2a\notin Q$; it lies at the node $(k,\,a\bmod 2^k)$, $k=\nu_2(b-a)$, and forces $\theta$ there to equal $\mathrm{bit}_k(b)$. A root pair is one with $b-a$ odd (node $(0,0)$); $Q$ is a true root release if every open root pair has even second entry, i.e. no open pair forces the value $1$ at the root. The sixteen-letter word
--   $$W_8=(0,1,3^8,3^4,3^{12},3^2,3^{10},3^6,3^{11},3^3,3^7,3^9,3^1,3^5,2\cdot3^{13},3^{13})$$
--   is $\theta$-safe for some tree witness $\theta$ and is a true root release. This is the case $j=8$ of the bit-reversal family $W_j$: even powers come in bit-reversal order of the half-exponent, and odd powers in decreasing bit-reversal order of $t+2$.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` are from `Definitions.Def_Erdos195_defs`. Positions are `List.idxOf`; the release property is stated as: every open in-order pair $(a,b)$ with $(b-a) \bmod 2 = 1$ has $b \bmod 2 = 0$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; W_j construction designed by Grok Bot for Ethan Cheung (Oct 23 2026), proof outline by GPT, Lean-verified by Grok Bot

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem W8_safe_released :
    let Q : List ℤ := [0, 1, 6561, 81, 531441, 9, 59049, 729, 177147, 27, 2187, 19683, 3, 243, 3188646, 1594323]
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) Q) ∧
    ∀ a b : ℤ, a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b → 2 * b - a ∉ Q → 3 * b - 2 * a ∉ Q →
      (b - a) % 2 = 1 → b % 2 = 0 := by sorry

end Erdos195
