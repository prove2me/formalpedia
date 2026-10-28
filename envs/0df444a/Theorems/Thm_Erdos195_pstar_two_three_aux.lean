-- Prove2me | Theorems.Thm_Erdos195_pstar_two_three_aux
-- name    : Erdos195.pstar_two_three_aux
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T05:41:53.05554+00:00
-- url     : https://prove2.me/theorems/5ee229c0-7d1f-4bf0-bbeb-5c288021f285
-- title:
--   Adding 2 to $P^*$ needs at least three auxiliary letters
-- statement:
--   Tree orders: for a tree witness $\theta(k,r)\in\{0,1\}$ and distinct integers $x,y$ with $k=\nu_2(y-x)$, $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ is $\theta$-safe if "$Q$ in order, then all other integers in $\prec_\theta$-order" has no monotone $4$-term arithmetic progression; it is tree-safe if it is $\theta$-safe for some $\theta$. An in-order pair $a$ before $b$ in $Q$ is open if $2b-a,3b-2a\notin Q$. Let $P^*=(0,1,-1,-5)$. If $Q$ is $\theta$-safe, begins with $P^*$ and contains $2$, then $3$ precedes $2$, and either $Q$ meets both $\{5,8\}$ and $\{9,16\}$, or $Q$ meets both $\{-2,-3\}$ and $\{-10,-15\}$. Consequently $Q$ has at least three distinct letters outside $\{-5,-1,0,1,2\}$.
--
--   Formalization note: `treeLt` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` from `Definitions.Def_Erdos195_defs`; positions are `List.idxOf`, $\nu_2$ is `padicValInt 2`, `L <+: Q` means $L$ is a prefix of $Q$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statement from GPT 6 Astra (Oct 23 2026 tree answers), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem pstar_two_three_aux (θ : ℕ → ℤ → Bool) (Q : List ℤ) (hS : Safe (treeLt θ) Q)
    (hpre : [0, 1, -1, -5] <+: Q) (h2 : (2 : ℤ) ∈ Q) :
    (3 ∈ Q ∧ Q.idxOf 3 < Q.idxOf 2) ∧
    (((5 ∈ Q ∨ 8 ∈ Q) ∧ (9 ∈ Q ∨ 16 ∈ Q)) ∨ ((-2 ∈ Q ∨ -3 ∈ Q) ∧ (-10 ∈ Q ∨ -15 ∈ Q))) ∧
    ∃ x ∈ Q, ∃ y ∈ Q, ∃ z ∈ Q, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      x ∉ [-5, -1, 0, 1, 2] ∧ y ∉ [-5, -1, 0, 1, 2] ∧ z ∉ [-5, -1, 0, 1, 2] := by sorry

end Erdos195
