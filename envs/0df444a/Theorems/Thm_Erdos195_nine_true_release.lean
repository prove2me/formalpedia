-- Prove2me | Theorems.Thm_Erdos195_nine_true_release
-- name    : Erdos195.nine_true_release
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T08:10:13.945648+00:00
-- url     : https://prove2.me/theorems/55a4320c-4f3e-4d9c-921e-867983ffa165
-- title:
--   A true root release after the prefix (0,1,9): the word (0,1,9,3,54,27)
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. An in-order pair $(a,b)$ of $Q$ ($a$ occurs before $b$) is open if $2b-a\notin Q$ and $3b-2a\notin Q$; it lies at the node $(k,\,a\bmod 2^k)$, $k=\nu_2(b-a)$, and forces $\theta$ there to equal $\mathrm{bit}_k(b)$. A root pair is one with $b-a$ odd (node $(0,0)$); $Q$ is a true root release if every open root pair has even second entry, i.e. no open pair forces the value $1$ at the root. The six-letter word
--   $$Q=(0,\ 1,\ 9,\ 3,\ 54,\ 27)$$
--   is tree-safe (with the witness $\theta(k,r)=1$ for $k\ge1$ and $\theta(0,0)=0$) and is a true root release: its open root pairs $(1,54),(9,54),(3,54)$ all have even second entry. Hence the root can be released after the three-letter prefix $(0,1,9)$. Here the forced $3$-chains of the odd letters $1$ and $9$ merge ($1\to3\to9\to27$), so a single grounded letter $27$ (preceded by $54$) suffices; for a general odd third letter $x$ the chains of $1$ and $x$ are disjoint and at least two grounded letters are needed (Erdős Problem 195, tree-witness approach).
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` are from `Definitions.Def_Erdos195_defs`. Positions are `List.idxOf`; "starts with 0" is `Q.head? = some 0`; the release hypothesis is stated as: every open in-order pair $(a,b)$ with $(b-a) \bmod 2 = 1$ has $b \bmod 2 = 0$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework, statements by Grok Bot for Ethan Cheung (hand reasoning, Oct 23 2026), Lean-verified

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem nine_true_release :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [0, 1, 9, 3, 54, 27]) ∧
    ∀ a b : ℤ, a ∈ [0, 1, 9, 3, 54, 27] → b ∈ [0, 1, 9, 3, 54, 27] →
      [0, 1, 9, 3, 54, 27].idxOf a < [0, 1, 9, 3, 54, 27].idxOf b →
      2 * b - a ∉ [0, 1, 9, 3, 54, 27] → 3 * b - 2 * a ∉ [0, 1, 9, 3, 54, 27] →
      (b - a) % 2 = 1 → b % 2 = 0 := by sorry

end Erdos195
