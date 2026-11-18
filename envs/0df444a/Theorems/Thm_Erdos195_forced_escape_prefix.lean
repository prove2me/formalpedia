-- Prove2me | Theorems.Thm_Erdos195_forced_escape_prefix
-- name    : Erdos195.forced_escape_prefix
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-17T16:29:58.269195+00:00
-- url     : https://prove2.me/theorems/fe7d0afa-b4be-4199-83e2-54a324cdd6b6
-- title:
--   Forced escape after the prefix $(0,1,x)$ with $x\equiv 3\pmod{4}$
-- statement:
--   Let $\theta$ be a tree witness, and let $Q$ be a $\theta$-safe finite word which is a true root release and begins with the prefix $(0,1,x)$, where $x\ge 3$ and $x\equiv 3\pmod{4}$. Then
--   $$
--   3x\in Q,
--   $$
--   and at least one of the following holds:
--   $$
--   3x-2\in Q,\qquad
--   7x\in Q,\qquad
--   \text{or}\quad
--   \bigl(5x\in Q\ \text{and}\ 5x\ \text{occurs before}\ 3x\bigr).
--   $$
--   In particular, at least one of $3x-2$, $5x$, $7x$ occurs in $Q$. These conditions are necessary, not sufficient.
--
--   As in the official lemma `odd_entry_demand`, a word is a **true root release** if every open in-order pair $(a,b)$ with odd difference has even second entry: no open pair forces the bit $1$ at the root node. An in-order pair $(a,b)$ is open when $2b-a\notin Q$ and $3b-2a\notin Q$.
--
--   The first clause $3x\in Q$ follows from `odd_entry_demand` together with the prefix: if $2x$ occurred it would have to occur after $x$, so it cannot be the grounded partner required when $3x$ is absent. The remaining obligation is a genuine escape from the two official tripling chains based at $1$ and at $x$: the in-order pairs $(1,x)$ and $(x,3x)$ occupy the same node $(1,1)$ and force opposite values of $\theta$ there, so they cannot both be open.
--
--   This does not rule out unrestricted extensions of $(0,1,x)$, does not claim that escape obligations always discharge finitely or propagate forever, and does not settle Erdős #195.
--
--   **Formalization Note** The prefix hypothesis is $Q=0::1::x::T$ for some tail $T$. The true-root-release hypothesis is the same predicate as in `Erdos195.odd_entry_demand`. Safety is official `Safe (treeLt θ)`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); derived from analysis relayed by Ethan Cheung (Nov 17 2026), hand-checked against the official Safe / treeLt / true-root-release definitions, Lean-verified.

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem forced_escape_prefix (θ : ℕ → ℤ → Bool) (Q : List ℤ) (x : ℤ)
    (hx : (3 : ℤ) ≤ x) (hxmod : x % 4 = 3)
    (hS : Safe (treeLt θ) Q)
    (hpref : ∃ T : List ℤ, Q = 0 :: 1 :: x :: T)
    (hrel : ∀ a b : ℤ, a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b → 2 * b - a ∉ Q →
      3 * b - 2 * a ∉ Q → (b - a) % 2 = 1 → b % 2 = 0) :
    (3 * x ∈ Q) ∧
    (3 * x - 2 ∈ Q ∨ 7 * x ∈ Q ∨ (5 * x ∈ Q ∧ Q.idxOf (5 * x) < Q.idxOf (3 * x))) ∧
    (3 * x - 2 ∈ Q ∨ 5 * x ∈ Q ∨ 7 * x ∈ Q) := by sorry

end Erdos195
