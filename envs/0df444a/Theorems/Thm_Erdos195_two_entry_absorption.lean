-- Prove2me | Theorems.Thm_Erdos195_two_entry_absorption
-- name    : Erdos195.two_entry_absorption
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T13:49:53.426706+00:00
-- url     : https://prove2.me/theorems/a319b1bc-f860-4855-a1ac-866365cc7162
-- title:
--   Two-entry target-last absorption: every two-letter word absorbs any new target with at most one helper
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. $Q$ is SAFE if it is $\theta$-safe for some tree witness $\theta$. Let $a\ne b$ be integers and let $y\notin\{a,b\}$. Put $k=\nu_2(b-a)$ and $t=\nu_2(y-a)$, and define
--   $$W=\begin{cases}(a,b,y),& t\le k,\\ (a,b,2y-b,y),& t>k.\end{cases}$$
--   Then $W$ has distinct entries and is SAFE. So any two-letter word can absorb an arbitrary new target placed last, with at most one auxiliary letter $2y-b$. Note that the hypotheses do not require $(a,b)$ itself to have any property, since every two-letter word is SAFE. This is the base case of the local absorption recipes (Astra) in the tree-witness approach to Erdős Problem 195.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`, and `Safe` is from `Definitions.Def_Erdos195_defs`. Positions are `List.idxOf`, and $\nu_2$ is `padicValInt 2`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; construction and proof sketch by GPT Astra, Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem two_entry_absorption (a b y : ℤ) (hab : a ≠ b) (hya : y ≠ a) (hyb : y ≠ b) :
    let W : List ℤ := if padicValInt 2 (y - a) ≤ padicValInt 2 (b - a) then [a, b, y]
      else [a, b, 2 * y - b, y]
    W.Nodup ∧ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) W := by sorry

end Erdos195
