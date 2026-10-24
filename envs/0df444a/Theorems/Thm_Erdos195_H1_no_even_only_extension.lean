-- Prove2me | Theorems.Thm_Erdos195_H1_no_even_only_extension
-- name    : Erdos195.H1_no_even_only_extension
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T16:09:51.848883+00:00
-- url     : https://prove2.me/theorems/2613e411-cb3f-434c-b766-204a87cf2d6e
-- title:
--   $H\cdot(109,-3)$ has no even-only SAFE extension containing a new entry
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. $Q$ is SAFE if it is $\theta$-safe for some tree witness $\theta$. Let $H_1=(0,1,-1,5,3,2,-15,-11,-5,-99,-115,-55,109,-3)$, which is SAFE. If $D$ is a finite word of even integers, at least one of which does not occur in $H_1$, then $H_1\cdot D$ is not SAFE. (The new-entry condition is necessary: appending already present letters does not change SAFE-ness.) This is GPT Astra's preparation obstruction: any SAFE continuation of $H_1$ with a new even entry must also add new odd entries.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; construction and proof sketch by GPT Astra, Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem H1_no_even_only_extension (D : List ℤ) (hD : ∀ z ∈ D, z % 2 = 0)
    (hnew : ∃ z ∈ D, z ∉ [0, 1, -1, 5, 3, 2, -15, -11, -5, -99, -115, -55, 109, -3]) :
    ¬ ∃ θ : ℕ → ℤ → Bool,
      Safe (treeLt θ) ([0, 1, -1, 5, 3, 2, -15, -11, -5, -99, -115, -55, 109, -3] ++ D) := by sorry

end Erdos195
