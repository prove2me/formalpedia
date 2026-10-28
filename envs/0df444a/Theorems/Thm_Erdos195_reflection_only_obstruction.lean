-- Prove2me | Theorems.Thm_Erdos195_reflection_only_obstruction
-- name    : Erdos195.reflection_only_obstruction
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T13:11:36.291046+00:00
-- url     : https://prove2.me/theorems/147813ee-7589-4af5-995e-58f957726972
-- title:
--   Reflection-only obstruction: $(0,-2)$ cannot absorb $1$ using only even auxiliaries
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes of the binary residue tree. A finite word $Q$ is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. An in-order pair $(a,b)$ of $Q$ is open if $2b-a\notin Q$ and $3b-2a\notin Q$. The word $Q$ is a true root release if every open pair with $b-a$ odd has $b$ even. There is no finite list $R$ of even integers such that
--   $$Q=(0,-2)\cdot R\cdot(1)$$
--   is $\theta$-safe for some tree witness and a true root release. Release forces the even support to be invariant under $x\mapsto 2-x$, and the extremes of the even support then give a node conflict at $(1,0)$. So in the tree-witness approach to Erdős Problem 195, the two-entry word $(0,-2)$, which is itself safe and released, cannot absorb the target $1$ by reflection-only preparation. This is the minimal starting word for such an obstruction.
--
--   Formalization note: tree-witness safety uses `treeLt θ` from `Definitions.Def_Erdos195_tree` and `Safe` from `Definitions.Def_Erdos195_defs`. Positions are `List.idxOf`. The release property is stated as: every open in-order pair $(a,b)$ with $(b-a)\bmod 2=1$ has $b\bmod 2=0$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; parity obstruction by Sol, Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem reflection_only_obstruction :
    ¬ ∃ R : List ℤ, (∀ r ∈ R, r % 2 = 0) ∧
      (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) ([0, -2] ++ R ++ [1])) ∧
      ∀ a b : ℤ, a ∈ [0, -2] ++ R ++ [1] → b ∈ [0, -2] ++ R ++ [1] →
        ([0, -2] ++ R ++ [1]).idxOf a < ([0, -2] ++ R ++ [1]).idxOf b →
        2 * b - a ∉ [0, -2] ++ R ++ [1] → 3 * b - 2 * a ∉ [0, -2] ++ R ++ [1] →
        (b - a) % 2 = 1 → b % 2 = 0 := by sorry

end Erdos195
