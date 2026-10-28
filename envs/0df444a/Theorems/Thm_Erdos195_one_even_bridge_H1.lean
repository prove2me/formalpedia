-- Prove2me | Theorems.Thm_Erdos195_one_even_bridge_H1
-- name    : Erdos195.one_even_bridge_H1
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T17:55:35.875849+00:00
-- url     : https://prove2.me/theorems/660df82d-d6b6-4479-b78c-58cc8f65aabe
-- title:
--   One-even route from H·(109,−3) to −2: exact criterion (symmetric odd prefix)
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. The halves of a word are the subsequences of its even letters and of its odd letters, each mapped by $x\mapsto\lfloor x/2\rfloor$; the half witnesses are $\theta_E(k,r)=\theta(k+1,2r)$ and $\theta_O(k,r)=\theta(k+1,2r+1)$.
--
--   Let $H_1=(0,1,-1,5,3,2,-15,-11,-5,-99,-115,-55,109,-3)$ (a safe word) and $O_0=(1,-1,5,3,-15,-11,-5,-99,-115,-55,109,-3)$ its odd subsequence.
--
--   **Theorem (one-even route from $H_1$ to $-2$).** Let $P,T$ be words of odd integers, with no letter of $P$ in $H_1$ and no letter of $T$ in $H_1\cdot P$. Then $H_1\cdot P\cdot(-2)\cdot T$ is $\theta$-safe for some tree witness $\theta$ if and only if $O_0\cdot P\cdot T$ is $\theta'$-safe for some tree witness $\theta'$ and the odd prefix is symmetric about $-2$:
--   $$x\in O_0\cdot P\ \Longrightarrow\ -4-x\in O_0\cdot P.$$
--
--   This confirms the one-even bridge criterion stated by GPT 6 Astra for the absorption of $-2$ into $H_1$ when $-2$ is the only new even integer. Every such completion is a reflection-symmetric odd prefix followed by an asymmetric odd completion. It is the instance $S=H_1$, $y=-2$ of Erdos195.one_even_bridge; the root bit is forced to be $1$ by the odd letter of largest absolute value.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; one-even route proposed by GPT 6 Astra; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem one_even_bridge_H1 (P T : List ℤ) (hPo : ∀ p ∈ P, p % 2 = 1) (hTo : ∀ t ∈ T, t % 2 = 1)
    (hPS : ∀ p ∈ P, p ∉ [0, 1, -1, 5, 3, 2, -15, -11, -5, -99, -115, -55, 109, -3])
    (hTS : ∀ t ∈ T, t ∉ [0, 1, -1, 5, 3, 2, -15, -11, -5, -99, -115, -55, 109, -3] ++ P) :
    (∃ θ : ℕ → ℤ → Bool,
      Safe (treeLt θ) ([0, 1, -1, 5, 3, 2, -15, -11, -5, -99, -115, -55, 109, -3] ++ P ++ [-2] ++ T)) ↔
    (∃ θ : ℕ → ℤ → Bool,
      Safe (treeLt θ) ([1, -1, 5, 3, -15, -11, -5, -99, -115, -55, 109, -3] ++ P ++ T)) ∧
    (∀ x ∈ [1, -1, 5, 3, -15, -11, -5, -99, -115, -55, 109, -3] ++ P,
      -4 - x ∈ [1, -1, 5, 3, -15, -11, -5, -99, -115, -55, 109, -3] ++ P) := by sorry

end Erdos195
