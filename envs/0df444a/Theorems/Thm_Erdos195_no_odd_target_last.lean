-- Prove2me | Theorems.Thm_Erdos195_no_odd_target_last
-- name    : Erdos195.no_odd_target_last
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T14:09:58.648149+00:00
-- url     : https://prove2.me/theorems/e26d83c6-c3a4-499f-bbea-8d2dd481a5a9
-- title:
--   No tree-safe word $(0,1,-1)\cdot R\cdot(2)$ with all auxiliaries odd
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. For letters $a$ before $b$ in $Q$, the pair $(a,b)$ is OPEN if neither $2b-a$ nor $3b-2a$ occurs in $Q$. There is no tree witness $\theta$ and no list $R$ of odd integers such that the word
--   $$(0,1,-1)\cdot R\cdot(2)$$
--   is $\theta$-safe. So in the tree-witness approach, the target $2$ cannot be absorbed last after $(0,1,-1)$ using only odd auxiliary letters; even helpers are necessary. (The asymmetric word $H$ of GPT Astra, which uses only odd repairs, accordingly places them after $2$.)
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`, and `Safe` is from `Definitions.Def_Erdos195_defs`. Positions are `List.idxOf`; the word is written `(0 :: 1 :: -1 :: rest) ++ [2]`, and the hypothesis $2\notin\mathrm{rest}$ makes $2$ the last letter and its only occurrence.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; argument by GPT Astra, Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem no_odd_target_last (R : List ℤ) (hR : ∀ r ∈ R, r % 2 = 1) :
    ¬ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) ((0 :: 1 :: -1 :: R) ++ [2]) := by sorry

end Erdos195
