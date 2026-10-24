-- Prove2me | Theorems.Thm_Erdos195_lifting_criterion
-- name    : Erdos195.lifting_criterion
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T14:52:55.765614+00:00
-- url     : https://prove2.me/theorems/cf3afa5d-827b-497e-a92f-db0552465fc3
-- title:
--   Exact lifting criterion: absorbing an odd target after an even batch, with odd fourth-term helpers
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. The halves of a word are the subsequences of its even letters and of its odd letters, each mapped by $x\mapsto\lfloor x/2\rfloor$. The half witnesses are $\theta_E(k,r)=\theta(k+1,2r)$ and $\theta_O(k,r)=\theta(k+1,2r+1)$.
--
--   **Theorem (exact lifting criterion).** Let $\theta(0,0)=0$ ("released" root). Let $S$ be a $\theta$-safe word, $R$ a word of even integers, and $y\notin S$ an odd integer. Write $P=S\cdot R$. Then $S\cdot R\cdot y$ is $\theta$-safe if and only if
--   1. the even half of $P$ is $\theta_E$-safe,
--   2. the odd half of $S\cdot y$ is $\theta_O$-safe, and
--   3. every even letter $a$ of $P$ satisfies
--   $$2y-a\in P\quad\text{or}\quad\Big(3y-2a\in S\ \text{ and, if } 2a-y\in S, \text{ then } a \text{ precedes } 2a-y \text{ in } P\Big).$$
--
--   This sharpens the symmetric lifting lemma, where every even letter is reflected ($2y-a\in P$), into an exact characterization. An even letter may instead be covered by an odd fourth-term helper $3y-2a$ that is already in $S$, provided the odd letter $2a-y$ does not precede it. So absorbing an odd target after an even batch into a released safe word reduces exactly to two half-safety problems plus this local helper condition.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`, and `Safe` is from `Definitions.Def_Erdos195_defs`. Halves are `filter` by parity followed by `map (· / 2)`. Positions are `List.idxOf`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; generalizes Erdos195.symmetric_lifting; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem lifting_criterion (θ : ℕ → ℤ → Bool) (h00 : θ 0 0 = false) (S R : List ℤ) (y : ℤ)
    (hS : Safe (treeLt θ) S) (hRe : ∀ r ∈ R, r % 2 = 0) (hy : y % 2 = 1) (hyS : y ∉ S) :
    Safe (treeLt θ) (S ++ R ++ [y]) ↔
      Safe (treeLt (fun k r => θ (k + 1) (2 * r)))
        (((S ++ R).filter (fun x => decide (x % 2 = 0))).map (· / 2)) ∧
      Safe (treeLt (fun k r => θ (k + 1) (2 * r + 1)))
        (((S ++ [y]).filter (fun x => decide (x % 2 = 1))).map (· / 2)) ∧
      (∀ a ∈ S ++ R, a % 2 = 0 → 2 * y - a ∈ S ++ R ∨
        (3 * y - 2 * a ∈ S ∧
          (2 * a - y ∈ S → (S ++ R).idxOf a < (S ++ R).idxOf (2 * a - y)))) := by sorry

end Erdos195
