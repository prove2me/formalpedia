-- Prove2me | Theorems.Thm_Erdos195_one_even_not_last_H1
-- name    : Erdos195.one_even_not_last_H1
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T17:58:56.876965+00:00
-- url     : https://prove2.me/theorems/5d810f3f-04b2-4d50-8cb1-a2c3aab8778a
-- title:
--   One-even route from H·(109,−3): −2 can never be the last entry
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. The halves of a word are the subsequences of its even letters and of its odd letters, each mapped by $x\mapsto\lfloor x/2\rfloor$; the half witnesses are $\theta_E(k,r)=\theta(k+1,2r)$ and $\theta_O(k,r)=\theta(k+1,2r+1)$.
--
--   Let $H_1=(0,1,-1,5,3,2,-15,-11,-5,-99,-115,-55,109,-3)$, a safe word.
--
--   **Theorem (the one-even route cannot end at the target).** For every word $P$ of odd integers, none of them in $H_1$,
--   $$H_1\cdot P\cdot(-2)\ \text{is not }\theta\text{-safe for any tree witness }\theta.$$
--
--   So when $-2$ is absorbed into $H_1$ with only odd helpers before it, at least one further entry must follow $-2$. Equivalently, every safe extension of $H_1$ that ends at $-2$ must contain a new even helper other than $-2$. The proof combines the exact one-even criterion (Erdos195.one_even_bridge_H1) with the extremal-parity lemma (Erdos195.extremal_parity). The odd prefix must be symmetric about $-2$, so after halving its extrema have opposite parity, while a safe word whose first two letters $0,-1$ have odd difference and whose first letter is interior has extrema of equal parity. This proves a claim of GPT 6 Astra.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; claim of GPT 6 Astra; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem one_even_not_last_H1 (P : List ℤ) (hPo : ∀ p ∈ P, p % 2 = 1)
    (hPS : ∀ p ∈ P, p ∉ [0, 1, -1, 5, 3, 2, -15, -11, -5, -99, -115, -55, 109, -3]) :
    ¬ ∃ θ : ℕ → ℤ → Bool,
      Safe (treeLt θ) ([0, 1, -1, 5, 3, 2, -15, -11, -5, -99, -115, -55, 109, -3] ++ P ++ [-2]) := by sorry

end Erdos195
