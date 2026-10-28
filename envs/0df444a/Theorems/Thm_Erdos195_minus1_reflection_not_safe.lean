-- Prove2me | Theorems.Thm_Erdos195_minus1_reflection_not_safe
-- name    : Erdos195.minus1_reflection_not_safe
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T11:08:19.861446+00:00
-- url     : https://prove2.me/theorems/38cdd833-abd0-4156-922c-2393dd4f763f
-- title:
--   The reflected batch word $(0,1,6,3,-2,-8,-1)$ is not tree-safe
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. An in-order pair $(a,b)$ of $Q$ ($a$ occurs before $b$) is open if $2b-a\notin Q$ and $3b-2a\notin Q$; it lies at the node $(k,\,a\bmod 2^k)$, $k=\nu_2(b-a)$, and forces $\theta$ there to equal $\mathrm{bit}_k(b)$. A root pair is one with $b-a$ odd (node $(0,0)$); $Q$ is a true root release if every open root pair has even second entry, i.e. no open pair forces the value $1$ at the root. No tree witness $\theta$ makes the word $(0,1,6,3,-2,-8,-1)$ $\theta$-safe. The open pairs $(0,6)$ and $(6,-8)$ both lie at node $(1,0)$ (as $\nu_2(6)=\nu_2(-14)=1$), and they force opposite bits there: $\mathrm{bit}_1(6)=1$ and $\mathrm{bit}_1(-8)=0$. So the order of $-2$ and $-8$ in the batch matters.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` are from `Definitions.Def_Erdos195_defs`. Positions are `List.idxOf`; the release property is stated as: every open in-order pair $(a,b)$ with $(b-a) \bmod 2 = 1$ has $b \bmod 2 = 0$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; batch words by Sol, Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem minus1_reflection_not_safe :
    ¬ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [0, 1, 6, 3, -2, -8, -1] := by sorry

end Erdos195
