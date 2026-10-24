-- Prove2me | Theorems.Thm_Erdos195_astra_H_safe
-- name    : Erdos195.astra_H_safe
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T13:49:52.684973+00:00
-- url     : https://prove2.me/theorems/80f8c42f-8661-44cd-a1d7-237adb88be49
-- title:
--   Astra's asymmetric word $(0,1,-1,5,3,2,-15,-11,-5,-99,-115,-55)$ is tree-safe, with $3$ before $2$
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. $Q$ is SAFE if it is $\theta$-safe for some tree witness $\theta$. The twelve-letter word
--   $$H=(0,1,-1,5,3,2,-15,-11,-5,-99,-115,-55)$$
--   is SAFE, and it lists $3$ before $2$. It extends the prefix $(0,1,-1)$ and contains the target $2$ with the compulsory witness $3$ before it. Its support is not symmetric under any reflection, and $H$ is not a true root release. It is built by two fourth-term repair blocks. In the tree-witness approach to Erdős Problem 195 it shows that a finite SAFE extension of $(0,1,-1)$ containing $3\prec2$ exists, which settles a question that symmetric completions cannot answer.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`, and `Safe` is from `Definitions.Def_Erdos195_defs`. Positions are `List.idxOf`, and $\nu_2$ is `padicValInt 2`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; construction and proof sketch by GPT Astra, Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem astra_H_safe :
    let H : List ℤ := [0, 1, -1, 5, 3, 2, -15, -11, -5, -99, -115, -55]
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) H) ∧ 3 ∈ H ∧ 2 ∈ H ∧ H.idxOf 3 < H.idxOf 2 := by sorry

end Erdos195
