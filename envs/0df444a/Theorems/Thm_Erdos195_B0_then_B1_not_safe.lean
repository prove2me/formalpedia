-- Prove2me | Theorems.Thm_Erdos195_B0_then_B1_not_safe
-- name    : Erdos195.B0_then_B1_not_safe
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T11:08:23.275687+00:00
-- url     : https://prove2.me/theorems/e1213b0c-2329-4346-af4f-9ffb800e40d6
-- title:
--   Concatenating the batches $B_0$ and $B_1$ is not tree-safe
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. An in-order pair $(a,b)$ of $Q$ ($a$ occurs before $b$) is open if $2b-a\notin Q$ and $3b-2a\notin Q$; it lies at the node $(k,\,a\bmod 2^k)$, $k=\nu_2(b-a)$, and forces $\theta$ there to equal $\mathrm{bit}_k(b)$. A root pair is one with $b-a$ odd (node $(0,0)$); $Q$ is a true root release if every open root pair has even second entry, i.e. no open pair forces the value $1$ at the root. No tree witness makes the $16$-letter word $(0,1,6,3,-8,-2,-1,-70,-78,-36,\,-40,-34,-17,-230,-270,-132)$ safe. This is $B_0$ followed by the $t=1$ batch of $B_1$. The in-order $3$-AP $(1,-8,-17)$ has its completion $-26$ missing from the word, which already violates safety. So the batches $B_t$ cannot simply be stacked.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` are from `Definitions.Def_Erdos195_defs`. Positions are `List.idxOf`; the release property is stated as: every open in-order pair $(a,b)$ with $(b-a) \bmod 2 = 1$ has $b \bmod 2 = 0$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; batch words by Sol, Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem B0_then_B1_not_safe :
    ¬ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ)
      [0, 1, 6, 3, -8, -2, -1, -70, -78, -36, -40, -34, -17, -230, -270, -132] := by sorry

end Erdos195
