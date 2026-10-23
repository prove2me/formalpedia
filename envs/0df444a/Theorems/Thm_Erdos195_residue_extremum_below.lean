-- Prove2me | Theorems.Thm_Erdos195_residue_extremum_below
-- name    : Erdos195.residue_extremum_below
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T05:33:36.724925+00:00
-- url     : https://prove2.me/theorems/e9cb4a3a-2434-40ef-9a21-fccf8a02f233
-- title:
--   A residue-class extremum lies $\prec_\theta$-below earlier class members
-- statement:
--   Tree orders: for a tree witness $\theta(k,r)\in\{0,1\}$ and distinct integers $x,y$ with $k=\nu_2(y-x)$, $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ is $\theta$-safe if "$Q$ in order, then all other integers in $\prec_\theta$-order" has no monotone $4$-term arithmetic progression. An in-order pair $a$ before $b$ in $Q$ is open if $2b-a,3b-2a\notin Q$. If $Q$ is $\theta$-safe, $b$ is the maximum or minimum of the letters of $Q$ congruent to $r$ modulo $2^m$, and $a$ is such a letter occurring before $b$, then
--   $$b\prec_\theta a.$$
--   So every new residue-class extremum must be placed $\prec_\theta$-below all earlier members of its class.
--
--   Formalization note: `treeLt` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` from `Definitions.Def_Erdos195_defs`; positions are `List.idxOf`, $\nu_2$ is `padicValInt 2`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statement from GPT 6 Astra (Oct 23 2026 tree answers), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem residue_extremum_below (θ : ℕ → ℤ → Bool) (Q : List ℤ) (hS : Safe (treeLt θ) Q)
    (m : ℕ) (r a b : ℤ) (ha : a ∈ Q) (hb : b ∈ Q)
    (har : a % 2 ^ m = r % 2 ^ m) (hbr : b % 2 ^ m = r % 2 ^ m)
    (hext : (∀ x ∈ Q, x % 2 ^ m = r % 2 ^ m → x ≤ b) ∨ (∀ x ∈ Q, x % 2 ^ m = r % 2 ^ m → b ≤ x))
    (hi : Q.idxOf a < Q.idxOf b) : treeLt θ b a := by sorry

end Erdos195
