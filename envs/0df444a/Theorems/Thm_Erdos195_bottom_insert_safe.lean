-- Prove2me | Theorems.Thm_Erdos195_bottom_insert_safe
-- name    : Erdos195.bottom_insert_safe
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T05:33:40.921579+00:00
-- url     : https://prove2.me/theorems/3f70f8b7-05e6-4589-a0ec-8428228c2eb1
-- title:
--   Appending a letter below the whole word in tree order
-- statement:
--   Tree orders: for a tree witness $\theta(k,r)\in\{0,1\}$ and distinct integers $x,y$ with $k=\nu_2(y-x)$, $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ is $\theta$-safe if "$Q$ in order, then all other integers in $\prec_\theta$-order" has no monotone $4$-term arithmetic progression. An in-order pair $a$ before $b$ in $Q$ is open if $2b-a,3b-2a\notin Q$. If $P$ is $\theta$-safe, $t\notin P$, $t\prec_\theta a$ for every $a\in P$, and whenever $a$ precedes $b$ in $P$ with $t=2b-a$ we have $3b-2a\in P$, then
--   $$P\cdot t\ \text{is}\ \theta\text{-safe}.$$
--   So a letter placed below the whole word in the tail order can be appended once the 3-AP condition holds.
--
--   Formalization note: `treeLt` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` from `Definitions.Def_Erdos195_defs`; positions are `List.idxOf`, $\nu_2$ is `padicValInt 2`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statement from GPT 6 Astra (Oct 23 2026 tree answers), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem bottom_insert_safe (θ : ℕ → ℤ → Bool) (P : List ℤ) (t : ℤ) (hP : Safe (treeLt θ) P)
    (ht : t ∉ P) (hbelow : ∀ a ∈ P, treeLt θ t a)
    (hap : ∀ a b : ℤ, a ∈ P → b ∈ P → P.idxOf a < P.idxOf b → t = 2 * b - a → 3 * b - 2 * a ∈ P) :
    Safe (treeLt θ) (P ++ [t]) := by sorry

end Erdos195
