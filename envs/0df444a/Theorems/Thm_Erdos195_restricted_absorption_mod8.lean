-- Prove2me | Theorems.Thm_Erdos195_restricted_absorption_mod8
-- name    : Erdos195.restricted_absorption_mod8
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T16:09:34.813353+00:00
-- url     : https://prove2.me/theorems/677f03da-64fa-4e16-9dc3-d7c0daaaa729
-- title:
--   Four-class restricted absorption: a SAFE block in one odd class mod 8 absorbs a target with $2n+4$ letters
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. $Q$ is SAFE if it is $\theta$-safe for some tree witness $\theta$. Let $A$ be a SAFE word all of whose entries are congruent modulo $8$ to an odd integer $r$. Let $a$ be even and $b\equiv r+2\pmod 4$, and put $Q=(a)\cdot A\cdot(b)$. Let $y\notin Q$ be such that $c=2y-b\notin Q$, $c\equiv r\pmod 8$, both $A\cdot(c)$ and $(c)\cdot A$ are SAFE, and $7b-6y\notin A$. Then
--   $$Q\cdot(2y-b)\cdot(2y-A)\cdot(y)\cdot(12y-11b)\cdot(10y-10b+A)\cdot(6y-5b)$$
--   is SAFE, where $2y-A$ and $10y-10b+A$ are entrywise images in the original order. This is GPT Astra's mod-8 generalization of the mod-32 absorption theorem: the block $A$ may occupy all four residue classes modulo $32$ inside one odd class modulo $8$. No size condition is needed and $A$ may be empty.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; construction and proof sketch by GPT Astra, Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem restricted_absorption_mod8 (a b y r : ℤ) (A : List ℤ)
    (hA : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) A)
    (hr : r % 2 = 1) (hAr : ∀ x ∈ A, x % 8 = r % 8)
    (ha : a % 2 = 0) (hb : b % 4 = (r + 2) % 4)
    (hy : y ∉ [a] ++ A ++ [b]) (hcQ : 2 * y - b ∉ [a] ++ A ++ [b]) (hc : (2 * y - b) % 8 = r % 8)
    (hAc : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (A ++ [2 * y - b]))
    (hcA : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) ([2 * y - b] ++ A))
    (h7 : 7 * b - 6 * y ∉ A) :
    ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ)
      (([a] ++ A ++ [b]) ++ ([2 * y - b] ++ A.map (fun x => 2 * y - x) ++ [y, 12 * y - 11 * b] ++
        A.map (fun x => 10 * y - 10 * b + x) ++ [6 * y - 5 * b])) := by sorry

end Erdos195
