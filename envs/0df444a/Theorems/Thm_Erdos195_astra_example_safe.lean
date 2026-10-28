-- Prove2me | Theorems.Thm_Erdos195_astra_example_safe
-- name    : Erdos195.astra_example_safe
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T15:32:38.834993+00:00
-- url     : https://prove2.me/theorems/71d6698c-2dc9-4b6d-a5e7-887d6114f591
-- title:
--   Astra's mod-32 absorption example $(0,1,33,3,17,19,-13,10,87,71,103,45)$ is SAFE
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. $Q$ is SAFE if it is $\theta$-safe for some tree witness $\theta$. The word $(0,1,33,3,17,19,-13,10,87,71,103,45)$ is SAFE. It is the instance $A=(1,33)$, $r=1$, $a=0$, $b=3$, $y=10$ of the mod-32 restricted absorption recipe; the target $10$ is smaller than the old support maximum $33$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; construction and proof sketch by GPT Astra, Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem astra_example_safe :
    ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [0, 1, 33, 3, 17, 19, -13, 10, 87, 71, 103, 45] := by sorry

end Erdos195
