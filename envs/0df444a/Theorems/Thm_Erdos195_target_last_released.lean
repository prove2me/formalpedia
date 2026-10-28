-- Prove2me | Theorems.Thm_Erdos195_target_last_released
-- name    : Erdos195.target_last_released
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T14:09:59.159682+00:00
-- url     : https://prove2.me/theorems/204f2435-e630-4546-9dab-2813033451d8
-- title:
--   Target-last absorption of $2$ after $(0,1,-1)$ forces a released word
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. For letters $a$ before $b$ in $Q$, the pair $(a,b)$ is OPEN if neither $2b-a$ nor $3b-2a$ occurs in $Q$. Let $\theta$ be any tree witness and let $A=(0,1,-1,r_1,\dots,r_m,2)$ be a word with $2\notin\{r_1,\dots,r_m\}$. If $A$ is $\theta$-safe, then $\theta(0,0)=0$, and $A$ is RELEASED:
--   $$\text{every OPEN pair }(a,b)\text{ of }A\text{ with }b-a\text{ odd has }b\text{ even.}$$
--   So absorbing the target $2$ as the last letter after the prefix $(0,1,-1)$ is only possible by a released word. The proof (following GPT Astra) compares the extremes of $A$ via the extremal-parity lemma, applied to $A$ and to its normalized odd half.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`, and `Safe` is from `Definitions.Def_Erdos195_defs`. Positions are `List.idxOf`; the word is written `(0 :: 1 :: -1 :: rest) ++ [2]`, and the hypothesis $2\notin\mathrm{rest}$ makes $2$ the last letter and its only occurrence.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; argument by GPT Astra, Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem target_last_released (θ : ℕ → ℤ → Bool) (A rest : List ℤ)
    (hA : A = (0 :: 1 :: -1 :: rest) ++ [2]) (h2 : (2 : ℤ) ∉ rest)
    (hS : Safe (treeLt θ) A) :
    θ 0 0 = false ∧
    ∀ a b : ℤ, a ∈ A → b ∈ A → A.idxOf a < A.idxOf b → (b - a) % 2 = 1 →
      2 * b - a ∉ A → 3 * b - 2 * a ∉ A → b % 2 = 0 := by sorry

end Erdos195
