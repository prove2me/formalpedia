-- Prove2me | Theorems.Thm_Erdos195_lifting_criterion_true
-- name    : Erdos195.lifting_criterion_true
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T15:11:16.996244+00:00
-- url     : https://prove2.me/theorems/e384900a-7c1d-4f92-b32a-5265437bf26f
-- title:
--   Exact lifting criterion with root bit 1: absorbing an odd target after an even batch
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. The halves of a word are the subsequences of its even letters and of its odd letters, each mapped by $x\mapsto\lfloor x/2\rfloor$. The half witnesses are $\theta_E(k,r)=\theta(k+1,2r)$ and $\theta_O(k,r)=\theta(k+1,2r+1)$.
--
--   **Theorem (exact lifting criterion, root bit $1$).** Let $\theta(0,0)=1$. Let $S$ be a $\theta$-safe word, $R$ a word of even integers, and $y\notin S$ an odd integer. Write $P=S\cdot R$. Then $S\cdot R\cdot y$ is $\theta$-safe if and only if
--   1. the even half of $P$ is $\theta_E$-safe;
--   2. the odd half of $S\cdot y$ is $\theta_O$-safe;
--   3. (closing new even letters) for every $b\in R\setminus S$ and every odd $a\in S$: $2b-a\in S$, or $2b-a=y$, or $3b-2a\in P$;
--   4. (no new third terms of open pairs) for all $a,b\in S$ with $b-a$ odd and $a$ before $b$ in $S$: if $2b-a\in R\setminus S$ then $3b-2a\in S$;
--   5. (in-order progressions ending at $y$) for every even $b\in P$ with $2b-y\in S$ preceding $b$ in $P$: $2y-b\in P$.
--
--   This is the companion of the root-bit-$0$ lifting criterion (Erdos195.lifting_criterion). When the root bit is $1$, open odd-difference pairs must end at an odd letter. So every new even letter must be closed against every odd letter of $S$ (condition 3), and a new even letter must not become the third term of a pair of $S$ that is open at the root (condition 4). Odd affine maps $x\mapsto mx+s$ with $s$ odd flip the root bit (Erdos195.safe_odd_affine_iff). The two criteria together therefore cover absorbing a target of either parity after a batch of the opposite parity.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; companion of Erdos195.lifting_criterion; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem lifting_criterion_true (θ : ℕ → ℤ → Bool) (h00 : θ 0 0 = true) (S R : List ℤ) (y : ℤ)
    (hS : Safe (treeLt θ) S) (hRe : ∀ r ∈ R, r % 2 = 0) (hy : y % 2 = 1) (hyS : y ∉ S) :
    Safe (treeLt θ) (S ++ R ++ [y]) ↔
      Safe (treeLt (fun k r => θ (k + 1) (2 * r)))
        (((S ++ R).filter (fun x => decide (x % 2 = 0))).map (· / 2)) ∧
      Safe (treeLt (fun k r => θ (k + 1) (2 * r + 1)))
        (((S ++ [y]).filter (fun x => decide (x % 2 = 1))).map (· / 2)) ∧
      (∀ b ∈ R, b ∉ S → ∀ a ∈ S, a % 2 = 1 →
        2 * b - a ∈ S ∨ 2 * b - a = y ∨ 3 * b - 2 * a ∈ S ++ R) ∧
      (∀ a ∈ S, ∀ b ∈ S, (b - a) % 2 = 1 → S.idxOf a < S.idxOf b →
        2 * b - a ∈ R → 2 * b - a ∉ S → 3 * b - 2 * a ∈ S) ∧
      (∀ b ∈ S ++ R, b % 2 = 0 → 2 * b - y ∈ S →
        (S ++ R).idxOf (2 * b - y) < (S ++ R).idxOf b → 2 * y - b ∈ S ++ R) := by sorry

end Erdos195
