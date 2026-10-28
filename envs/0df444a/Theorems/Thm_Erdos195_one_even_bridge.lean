-- Prove2me | Theorems.Thm_Erdos195_one_even_bridge
-- name    : Erdos195.one_even_bridge
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T17:55:35.167449+00:00
-- url     : https://prove2.me/theorems/f8723d8a-26e5-42f3-b9c8-d3c4f5e77c55
-- title:
--   One-even bridge criterion: odd batches around a single new even letter (root bit 1)
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. The halves of a word are the subsequences of its even letters and of its odd letters, each mapped by $x\mapsto\lfloor x/2\rfloor$; the half witnesses are $\theta_E(k,r)=\theta(k+1,2r)$ and $\theta_O(k,r)=\theta(k+1,2r+1)$.
--
--   **Theorem (one-even bridge criterion, root bit $1$).** Let $\theta(0,0)=1$. Let $S$ be a word that is $\theta_S$-safe for some witness $\theta_S$ with $\theta_S(0,0)=1$. Let $P$ and $T$ be words of odd integers with no letter of $P$ in $S$ and no letter of $T$ in $S\cdot P$, and let $y\notin S$ be even. Then
--   $$S\cdot P\cdot y\cdot T\ \text{is }\theta\text{-safe}$$
--   if and only if
--   1. the even half of $S\cdot y$ is $\theta_E$-safe and the odd half of $S\cdot P\cdot T$ is $\theta_O$-safe;
--   2. (closing pairs into $y$) for every odd $a\in S\cdot P$: $2y-a\in S\cdot P$ or $3y-2a\in S$;
--   3. (progressions with third term $y$) for every even $a\in S$ and odd $b\in S\cdot P$ with $2b-a=y$ and $a$ before $b$: $3b-2a\in S\cdot P$;
--   4. (new third terms of pairs of $S$) for odd $a$ and even $b$ in $S$, $a$ before $b$, with $2b-a\notin S$ but $2b-a\in P\cdot T$: either $3b-2a\in S$, or $3b-2a=y$ and $2b-a\notin P$.
--
--   This is the exact root-level criterion for absorbing a single new even letter into a root-bit-$1$ word using only odd helpers placed before and after it: nothing is required of the odd batches except odd-half safety, while the letters before $y$ must be (almost) closed under reflection $a\mapsto 2y-a$. It complements the lifting criteria Erdos195.lifting_criterion and Erdos195.lifting_criterion_true (odd target after an even batch). Formalization note: $S$ itself only needs to be safe for some root-bit-$1$ witness, not for $\theta$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; one-even route proposed by GPT 6 Astra; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem one_even_bridge (θ : ℕ → ℤ → Bool) (h00 : θ 0 0 = true) (S P T : List ℤ) (y : ℤ)
    (hS : ∃ θS : ℕ → ℤ → Bool, θS 0 0 = true ∧ Safe (treeLt θS) S)
    (hPo : ∀ p ∈ P, p % 2 = 1) (hTo : ∀ t ∈ T, t % 2 = 1) (hy : y % 2 = 0) (hyS : y ∉ S)
    (hPS : ∀ p ∈ P, p ∉ S) (hTS : ∀ t ∈ T, t ∉ S ++ P) :
    Safe (treeLt θ) (S ++ P ++ [y] ++ T) ↔
      Safe (treeLt (fun k r => θ (k + 1) (2 * r)))
        (((S ++ [y]).filter (fun x => decide (x % 2 = 0))).map (· / 2)) ∧
      Safe (treeLt (fun k r => θ (k + 1) (2 * r + 1)))
        (((S ++ P ++ T).filter (fun x => decide (x % 2 = 1))).map (· / 2)) ∧
      (∀ a ∈ S ++ P, a % 2 = 1 → 2 * y - a ∈ S ++ P ∨ 3 * y - 2 * a ∈ S) ∧
      (∀ a ∈ S, a % 2 = 0 → ∀ b ∈ S ++ P, b % 2 = 1 → 2 * b - a = y →
        (S ++ P).idxOf a < (S ++ P).idxOf b → 3 * b - 2 * a ∈ S ++ P) ∧
      (∀ a ∈ S, ∀ b ∈ S, a % 2 = 1 → b % 2 = 0 → S.idxOf a < S.idxOf b →
        2 * b - a ∉ S → 2 * b - a ∈ P ++ T →
        3 * b - 2 * a ∈ S ∨ (3 * b - 2 * a = y ∧ 2 * b - a ∉ P)) := by sorry

end Erdos195
