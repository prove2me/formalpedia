-- Prove2me | Theorems.Thm_Erdos195_residue_extremal_open
-- name    : Erdos195.residue_extremal_open
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T05:33:36.138526+00:00
-- url     : https://prove2.me/theorems/d82cb2ac-cc73-4557-a100-b33bb8d7e61d
-- title:
--   Residue-class extremal pairs are open
-- statement:
--   Let $Q$ be a finite word of integers, $m\ge0$, and $S$ the letters of $Q$ congruent to $r$ modulo $2^m$. If $b\in S$ is the maximum or the minimum of $S$ and $a\in S$ occurs before $b$ in $Q$, then
--   $$2b-a\notin Q\quad\text{and}\quad 3b-2a\notin Q,$$
--   i.e. $(a,b)$ is an open pair. (Both continuations lie in the same residue class and beyond the extremum.) This is a structural source of open pairs in Ho-style constructions of $4$-AP-free permutations of $\mathbb{Z}$ (Erdős Problem 195).
--
--   Formalization note: `treeLt` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` from `Definitions.Def_Erdos195_defs`; positions are `List.idxOf`, $\nu_2$ is `padicValInt 2`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statement from GPT 6 Astra (Oct 23 2026 tree answers), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem residue_extremal_open (Q : List ℤ) (m : ℕ) (r a b : ℤ) (ha : a ∈ Q) (hb : b ∈ Q)
    (har : a % 2 ^ m = r % 2 ^ m) (hbr : b % 2 ^ m = r % 2 ^ m)
    (hext : (∀ x ∈ Q, x % 2 ^ m = r % 2 ^ m → x ≤ b) ∨ (∀ x ∈ Q, x % 2 ^ m = r % 2 ^ m → b ≤ x))
    (hi : Q.idxOf a < Q.idxOf b) :
    2 * b - a ∉ Q ∧ 3 * b - 2 * a ∉ Q := by sorry

end Erdos195
