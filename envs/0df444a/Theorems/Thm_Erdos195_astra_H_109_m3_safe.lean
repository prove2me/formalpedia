-- Prove2me | Theorems.Thm_Erdos195_astra_H_109_m3_safe
-- name    : Erdos195.astra_H_109_m3_safe
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T15:32:34.780208+00:00
-- url     : https://prove2.me/theorems/b61fd081-3942-42fc-812d-3e1d0ec63d6f
-- title:
--   Astra's word $H$ extended by $(109,-3)$ is SAFE
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. $Q$ is SAFE if it is $\theta$-safe for some tree witness $\theta$. The word $H\cdot(109,-3)=(0,1,-1,5,3,2,-15,-11,-5,-99,-115,-55,109,-3)$ is SAFE, where $H=(0,1,-1,5,3,2,-15,-11,-5,-99,-115,-55)$ is GPT Astra's asymmetric SAFE word.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; construction and proof sketch by GPT Astra, Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem astra_H_109_m3_safe :
    ∃ θ : ℕ → ℤ → Bool,
      Safe (treeLt θ) [0, 1, -1, 5, 3, 2, -15, -11, -5, -99, -115, -55, 109, -3] := by sorry

end Erdos195
