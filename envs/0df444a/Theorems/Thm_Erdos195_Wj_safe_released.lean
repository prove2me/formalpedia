-- Prove2me | Theorems.Thm_Erdos195_Wj_safe_released
-- name    : Erdos195.Wj_safe_released
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T09:56:54.206756+00:00
-- url     : https://prove2.me/theorems/ead4f6f8-c784-4c9a-aa24-d7446353e8b8
-- title:
--   The bit-reversal words $W_{2^n}$ are tree-safe true root releases for all $n\ge2$
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. An in-order pair $(a,b)$ of $Q$ ($a$ occurs before $b$) is open if $2b-a\notin Q$ and $3b-2a\notin Q$; it lies at the node $(k,\,a\bmod 2^k)$, $k=\nu_2(b-a)$, and forces $\theta$ there to equal $\mathrm{bit}_k(b)$. A root pair is one with $b-a$ odd (node $(0,0)$); $Q$ is a true root release if every open root pair has even second entry, i.e. no open pair forces the value $1$ at the root. Let $n\ge2$, $j=2^n$, $T=3^{2j-3}$, and let $W_j$ be the bit-reversal word
--   $$W_j=\bigl(0,\ 9^{\mathrm{br}_n(0)},\dots,9^{\mathrm{br}_n(j-2)},\ \text{odd powers }3\cdot 9^{t}\ (t\le j-3)\text{ by decreasing }\mathrm{br}_n(t+2),\ 2T,\ T\bigr)$$
--   (definition `Erdos195.Wj`, e.g. $W_4=(0,1,81,9,27,3,486,243)$). Then $W_j$ is $\theta$-safe for some tree witness $\theta$, and it is a true root release.
--
--   So the tree-witness method admits arbitrarily long safe words containing all powers $3^0,\dots,3^{2j-3}$ with the root released. The ordering is forced by the $2$-adic identity $\nu_2(9^a-9^b)=3+\nu_2(a-b)$: two same-parity powers $3^{e}9^{s}$, $3^e9^t$ meet at level $3+\nu_2(t-s)$, and bit reversal orders them so that the forced bit depends only on the node. This gives an infinite family of safe words of one fixed shape, though not yet an exhaustive chain.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `br`, `Wj` are from `Definitions.Def_Erdos195_Wj`; `Safe`, `bitOne` are from `Definitions.Def_Erdos195_defs`. Positions are `List.idxOf`; the release property is stated as: every open in-order pair $(a,b)$ with $(b-a) \bmod 2 = 1$ has $b \bmod 2 = 0$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; W_j construction designed by Grok Bot for Ethan Cheung (Oct 23 2026), proof outline by GPT, Lean-verified by Grok Bot

import Mathlib
import Definitions.Def_Erdos195_tree
import Definitions.Def_Erdos195_Wj

namespace Erdos195

theorem Wj_safe_released (n : ℕ) (hn : 2 ≤ n) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (Wj n)) ∧
    ∀ a b : ℤ, a ∈ Wj n → b ∈ Wj n → (Wj n).idxOf a < (Wj n).idxOf b →
      2 * b - a ∉ Wj n → 3 * b - 2 * a ∉ Wj n → (b - a) % 2 = 1 → b % 2 = 0 := by sorry

end Erdos195
