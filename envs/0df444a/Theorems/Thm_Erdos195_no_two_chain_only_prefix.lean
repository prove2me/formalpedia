-- Prove2me | Theorems.Thm_Erdos195_no_two_chain_only_prefix
-- name    : Erdos195.no_two_chain_only_prefix
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-17T16:33:24.761664+00:00
-- url     : https://prove2.me/theorems/6864bbc2-bb5f-40e8-a6eb-0230807f1224
-- title:
--   No two-chain-only true root release beginning $(0,1,x)$ with $x\equiv 3\pmod{4}$
-- statement:
--   Let $\theta$ be a tree witness, and let $Q$ be a $\theta$-safe true root release beginning with the prefix $(0,1,x)$, where $x\ge 3$ and $x\equiv 3\pmod{4}$. There is no such word whose odd entries all belong to the two chains
--   $$
--   S_x=\{3^n:n\ge 0\}\cup\{x\cdot 3^n:n\ge 0\}.
--   $$
--   There is no restriction on the even entries of $Q$.
--
--   The reason is the forced-escape lemma: an odd letter from $\{3x-2,5x,7x\}$ must occur. None of these lies in $S_x$. Indeed $3x-2\ge 7$ is $1\pmod{3}$, so it is not a positive power of $3$, and $x$ does not divide $3x-2$ because $x$ does not divide $2$; while $5x=3^n$ would make $5$ divide a power of $3$, and $5x=x\cdot 3^n$ would force $5=3^n$, and likewise with $7$ in place of $5$.
--
--   In particular this rules out every chain-only construction beginning $(0,1,3^j)$ with $j$ odd, including the $x=15$ and $x=27$ attempts that only extend $1\to 3\to 9\to\cdots$ and $x\to 3x\to 9x\to\cdots$ together with even (doubled) companions. The lemma does not rule out unrestricted extensions, and it does not settle Erdős #195.
--
--   **Formalization Note** The prefix and true-root-release hypotheses match `Erdos195.forced_escape_prefix`. Membership in $S_x$ is expressed as $\exists n,\ z=3^n\lor z=x\cdot 3^n$ for every odd letter $z$ of $Q$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); derived from analysis relayed by Ethan Cheung (Nov 17 2026), hand-checked against the official Safe / treeLt / true-root-release definitions, Lean-verified.

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem no_two_chain_only_prefix (θ : ℕ → ℤ → Bool) (Q : List ℤ) (x : ℤ)
    (hx : (3 : ℤ) ≤ x) (hxmod : x % 4 = 3)
    (hS : Safe (treeLt θ) Q)
    (hpref : ∃ T : List ℤ, Q = 0 :: 1 :: x :: T)
    (hrel : ∀ a b : ℤ, a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b → 2 * b - a ∉ Q →
      3 * b - 2 * a ∉ Q → (b - a) % 2 = 1 → b % 2 = 0)
    (hodd : ∀ z ∈ Q, z % 2 = 1 →
      ∃ n : ℕ, z = (3 : ℤ) ^ n ∨ z = x * (3 : ℤ) ^ n) :
    False := by sorry

end Erdos195
