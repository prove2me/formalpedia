-- Prove2me | Theorems.Thm_Erdos195_pstar_two_four_aux
-- name    : Erdos195.pstar_two_four_aux
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T05:41:53.202231+00:00
-- url     : https://prove2.me/theorems/9f2efbef-e926-4644-8453-a5ac53659ee2
-- title:
--   Adding 2 to $P^*$ needs at least four auxiliary letters
-- statement:
--   Tree orders: for a tree witness $\theta(k,r)\in\{0,1\}$ and distinct integers $x,y$ with $k=\nu_2(y-x)$, $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ is $\theta$-safe if "$Q$ in order, then all other integers in $\prec_\theta$-order" has no monotone $4$-term arithmetic progression; it is tree-safe if it is $\theta$-safe for some $\theta$. An in-order pair $a$ before $b$ in $Q$ is open if $2b-a,3b-2a\notin Q$. Let $P^*=(0,1,-1,-5)$. Let $Q$ be $\theta$-safe, beginning with $P^*$ and containing $2$. (A) If $Q$ meets both $\{-2,-3\}$ and $\{-10,-15\}$, then $-3,-15\in Q$ and $Q$ meets $\{-11,-17,-29,-43\}$. (B) Otherwise $Q$ meets $\{5,8\}$ and $\{9,16\}$, $8\in Q$ forces $Q$ to meet $\{17,26\}$, and $5\in Q$ forces $Q$ to meet $\{-11,-17,15,25\}$. In all cases
--   $$Q\ \text{has at least four distinct letters outside}\ \{-5,-1,0,1,2\}.$$
--
--   Formalization note: `treeLt` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` from `Definitions.Def_Erdos195_defs`; positions are `List.idxOf`, $\nu_2$ is `padicValInt 2`, `L <+: Q` means $L$ is a prefix of $Q$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statement from GPT 6 Astra (Oct 23 2026 tree answers), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem pstar_two_four_aux (θ : ℕ → ℤ → Bool) (Q : List ℤ) (hS : Safe (treeLt θ) Q)
    (hpre : [0, 1, -1, -5] <+: Q) (h2 : (2 : ℤ) ∈ Q) :
    (((-2 ∈ Q ∨ -3 ∈ Q) ∧ (-10 ∈ Q ∨ -15 ∈ Q)) →
      -3 ∈ Q ∧ -15 ∈ Q ∧ (-11 ∈ Q ∨ -17 ∈ Q ∨ -29 ∈ Q ∨ -43 ∈ Q)) ∧
    (¬ ((-2 ∈ Q ∨ -3 ∈ Q) ∧ (-10 ∈ Q ∨ -15 ∈ Q)) →
      ((5 ∈ Q ∨ 8 ∈ Q) ∧ (9 ∈ Q ∨ 16 ∈ Q)) ∧ (8 ∈ Q → 17 ∈ Q ∨ 26 ∈ Q) ∧
      (5 ∈ Q → -11 ∈ Q ∨ -17 ∈ Q ∨ 15 ∈ Q ∨ 25 ∈ Q)) ∧
    ∃ x ∈ Q, ∃ y ∈ Q, ∃ z ∈ Q, ∃ w ∈ Q, [x, y, z, w].Nodup ∧
      ∀ e ∈ [x, y, z, w], e ∉ [-5, -1, 0, 1, 2] := by sorry

end Erdos195
