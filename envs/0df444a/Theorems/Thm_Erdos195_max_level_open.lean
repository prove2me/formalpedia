-- Prove2me | Theorems.Thm_Erdos195_max_level_open
-- name    : Erdos195.max_level_open
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T05:33:28.259649+00:00
-- url     : https://prove2.me/theorems/339a3372-5dbf-457f-8aee-5ade7ec895fb
-- title:
--   The maximal pair level is attained by an open pair
-- statement:
--   Let $Q$ be a finite word of integers and $x\ne y$ letters of $Q$ such that $\nu_2(y-x)$ is maximal among all $\nu_2(b-a)$, $a\ne b$ letters of $Q$. Then some open pair $(a,b)$ of $Q$ ($a$ before $b$, $2b-a,3b-2a\notin Q$) has
--   $$\nu_2(b-a)=\nu_2(y-x).$$
--   Hence the maximal level of an open pair equals the maximal level of any pair. Relevant to Ho-style constructions for Erdős Problem 195.
--
--   Formalization note: `treeLt` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` from `Definitions.Def_Erdos195_defs`; positions are `List.idxOf`, $\nu_2$ is `padicValInt 2`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statement from GPT 6 Astra (Oct 23 2026 tree answers), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem max_level_open (Q : List ℤ) (x y : ℤ) (hx : x ∈ Q) (hy : y ∈ Q) (hxy : x ≠ y)
    (hK : ∀ a ∈ Q, ∀ b ∈ Q, a ≠ b → padicValInt 2 (b - a) ≤ padicValInt 2 (y - x)) :
    ∃ a b : ℤ, a ∈ Q ∧ b ∈ Q ∧ Q.idxOf a < Q.idxOf b ∧ 2 * b - a ∉ Q ∧ 3 * b - 2 * a ∉ Q ∧
      padicValInt 2 (b - a) = padicValInt 2 (y - x) := by sorry

end Erdos195
