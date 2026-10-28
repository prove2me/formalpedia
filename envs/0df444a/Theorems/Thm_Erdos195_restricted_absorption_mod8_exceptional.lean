-- Prove2me | Theorems.Thm_Erdos195_restricted_absorption_mod8_exceptional
-- name    : Erdos195.restricted_absorption_mod8_exceptional
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T20:02:36.195459+00:00
-- url     : https://prove2.me/theorems/68d71fd1-578f-442b-9530-ca0c84b952ba
-- title:
--   Four-class restricted absorption, exceptional case (7b−6y ∈ A): reorder the reflections with 4y−3b last
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$ (milestone framework). A finite word $W$ of integers is SAFE for $\theta$ if the sequence "letters of $W$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression. **Theorem (exceptional case of the four-class absorption theorem).** Let $r$ be odd, let $A$ be a list of integers all $\equiv r \pmod 8$, let $a$ be even and $b\equiv r+2\pmod 4$, and put $Q=(a)\cdot A\cdot(b)$. Let $y\notin Q$ and $c=2y-b\notin Q$ with $c\equiv r\pmod 8$, and assume both $A\cdot(c)$ and $(c)\cdot A$ are SAFE (for some witnesses). Suppose $7b-6y\in A$ but $10y-9b\notin A$. Put $w=6y-5b$ and $t=4y-3b$. Then there is a duplicate-free list $L$ whose entries are exactly the elements of $\{12y-11b\}\cup(10y-10b+A)$ other than $t$, such that
--   $$Q\cdot(c)\cdot(2y-A)\cdot(y)\cdot L\cdot(w,t)$$
--   is SAFE for some tree witness.
--
--   This is the exceptional case ($7b-6y\in A$) of GPT 6 Astra's four-class restricted absorption theorem. The non-exceptional case is milestone #122. Together they cover Astra's full critical exclusion $\{7b-6y,\,10y-9b\}\not\subseteq A$. When $7b-6y\in A$, the closed-form batch fails because $t=2c-b$ lies in the reflection block. The fix: order the reflection set safely with $t$ last (specified-last-entry ordering, milestone #133) and put $w$ before $t$. The proof uses the two-child decomposition at the root (the even letters are $a,y$; odd-to-$y$ pairs close by reflection about $y$) and at level 1 of the odd class. In the odd class, every cross 3-AP gets its fourth term in time; the only new case is $(b,c,t)$, whose fourth term $w$ now comes before $t$, and $(8y-7b,w,t)$, whose fourth term $c$ is old. The hypothesis $10y-9b\notin A$ rules out the cross triple $(10y-9b,\,8y-7b,\,w)$, whose fourth term would be the delayed $t$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026); theorem of GPT 6 Astra (astra_fourclass)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem restricted_absorption_mod8_exceptional (a b y r : ℤ) (A : List ℤ)
    (hr : r % 2 = 1) (hAr : ∀ x ∈ A, x % 8 = r % 8)
    (ha : a % 2 = 0) (hb : b % 4 = (r + 2) % 4)
    (hy : y ∉ [a] ++ A ++ [b]) (hcQ : 2 * y - b ∉ [a] ++ A ++ [b]) (hc : (2 * y - b) % 8 = r % 8)
    (hAc : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (A ++ [2 * y - b]))
    (hcA : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) ([2 * y - b] ++ A))
    (h7 : 7 * b - 6 * y ∈ A) (h10 : 10 * y - 9 * b ∉ A) :
    ∃ L : List ℤ, L.Nodup ∧
      (∀ x, x ∈ L ↔ (x = 12 * y - 11 * b ∨ ∃ v ∈ A, x = 10 * y - 10 * b + v) ∧ x ≠ 4 * y - 3 * b) ∧
      ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ)
        (([a] ++ A ++ [b]) ++ ([2 * y - b] ++ A.map (fun x => 2 * y - x) ++ [y] ++ L ++
          [6 * y - 5 * b, 4 * y - 3 * b])) := by sorry

end Erdos195
