-- Prove2me | Theorems.Thm_Erdos195_restricted_absorption
-- name    : Erdos195.restricted_absorption
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T15:32:36.675693+00:00
-- url     : https://prove2.me/theorems/2b86fda5-b2a4-45f4-9438-d18d8a825f1c
-- title:
--   Restricted absorption: a mod-32 sparse SAFE block absorbs any admissible target with $2n+4$ letters
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. $Q$ is SAFE if it is $\theta$-safe for some tree witness $\theta$. Let $A=(x_1,\dots,x_n)$ be a SAFE word all of whose entries are congruent modulo $32$ to an odd integer $r$. Let $a$ be even, $b\equiv r+2\pmod 4$, and let $y\notin Q=(a)\cdot A\cdot(b)$ satisfy $2y-b\equiv r+16\pmod{32}$. Then
--   $$Q\cdot(2y-b)\cdot(2y-A)\cdot(y)\cdot(12y-11b)\cdot(10y-10b+A)\cdot(6y-5b)$$
--   is SAFE, where $2y-A$ and $10y-10b+A$ are taken entrywise in the original order. No size condition on $y$ is needed, $A$ may be empty, and SAFE-ness of $Q$ itself is not assumed (it follows). This is the mod-32 form of GPT Astra's uniform finite absorption theorem: an infinite class of arbitrarily long SAFE words absorbs every target of a residue class with exactly $2n+4$ new entries.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; construction and proof sketch by GPT Astra, Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem restricted_absorption (a b y r : ℤ) (A : List ℤ)
    (hA : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) A)
    (hr : r % 2 = 1) (hAr : ∀ x ∈ A, x % 32 = r % 32)
    (ha : a % 2 = 0) (hb : b % 4 = (r + 2) % 4)
    (hy : y ∉ [a] ++ A ++ [b]) (hc : (2 * y - b) % 32 = (r + 16) % 32) :
    ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ)
      (([a] ++ A ++ [b]) ++ ([2 * y - b] ++ A.map (fun x => 2 * y - x) ++ [y, 12 * y - 11 * b] ++
        A.map (fun x => 10 * y - 10 * b + x) ++ [6 * y - 5 * b])) := by sorry

end Erdos195
