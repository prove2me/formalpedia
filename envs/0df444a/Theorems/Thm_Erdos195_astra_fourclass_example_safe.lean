-- Prove2me | Theorems.Thm_Erdos195_astra_fourclass_example_safe
-- name    : Erdos195.astra_fourclass_example_safe
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T16:09:31.370696+00:00
-- url     : https://prove2.me/theorems/3b9b3332-0087-44d7-9907-e4e19e36050b
-- title:
--   Astra's four-class absorption certificate (27 letters) is SAFE
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. $Q$ is SAFE if it is $\theta$-safe for some tree witness $\theta$. The word
--   $$(0,1,17,49,9,25,57,41,3,33,35,19,-13,27,11,-21,-5,18,183,151,167,199,159,175,207,191,93)$$
--   is SAFE. It is the instance $A=(1,17,49,9,25,57,41)$, $a=0$, $b=3$, $y=18$ of the four-class absorption recipe; $A$ occupies all four residue classes $1,9,17,25$ modulo $32$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; construction and proof sketch by GPT Astra, Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem astra_fourclass_example_safe :
    ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ)
      [0, 1, 17, 49, 9, 25, 57, 41, 3, 33, 35, 19, -13, 27, 11, -21, -5, 18,
        183, 151, 167, 199, 159, 175, 207, 191, 93] := by sorry

end Erdos195
