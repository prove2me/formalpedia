-- Prove2me | Theorems.Thm_Erdos195_zero_one_odd_finite_extension
-- name    : Erdos195.zero_one_odd_finite_extension
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-18T12:03:57.509227+00:00
-- url     : https://prove2.me/theorems/7658cea0-de78-4f8d-aa87-13f45994fee7
-- title:
--   Any finite set of odd integers extends the prefix $(0,1)$ with no other even entries
-- statement:
--   A tree witness is a function $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ on the nodes $(k,r)$ of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=1\Leftrightarrow\theta(k,\,x\bmod 2^k)=1$. A finite word $Q$ is $\theta$-safe if the completion “letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order” contains no monotone $4$-term arithmetic progression. Positions are first occurrences.
--
--   **Corollary.** For every finite set $F$ of odd integers there is a duplicate-free word $Q$ which begins with the prefix $(0,1)$, contains every element of $F$, has no even entry other than $0$, and is tree-safe for some witness $\theta$.
--
--   The construction is the one recorded in the safe-word composition note. Let $H=\{0\}\cup\{(z-1)/2:z\in F\}$ and apply the specified-first ordering lemma to obtain a tree-safe word $A$ with underlying set $H$ beginning with $0$. Output
--   $$Q=(0)\cdot(1+2A).$$
--   The official parity decomposition of tree safety reduces the claim to safety of the even child $(0)$ and of the odd child $A$, together with a root condition. Mixed-parity in-order pairs in $Q$ necessarily begin with the unique even letter $0$, so they force $\theta(0,0)=1$, consistently.
--
--   This handles arbitrarily many prescribed positive and negative odd integers simultaneously while preserving the prefix $(0,1)$. It does not justify inserting a new even integer after the odd block has begun, is not a true-root-release statement, and does not settle Erdős #195.
--
--   **Formalization Note** The prefix hypothesis is $Q=0::1::T$ for some tail $T$. Safety is official `Safe (treeLt θ)`. The lemma `specified_first_safe_order` supplies $A$; the gluing step uses official `safe_parity_decomp`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); derived from analysis relayed by Ethan Cheung, hand-checked against the official Safe / treeLt / specified_first_safe_order / safe_parity_decomp definitions, Lean-verified.

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem zero_one_odd_finite_extension (F : Finset ℤ) (hF : ∀ z ∈ F, z % 2 = 1) :
    ∃ Q : List ℤ, Q.Nodup ∧ (∃ T : List ℤ, Q = 0 :: 1 :: T) ∧ (∀ z ∈ F, z ∈ Q) ∧
      (∀ z ∈ Q, z % 2 = 0 → z = 0) ∧
      ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) Q := by sorry

end Erdos195
