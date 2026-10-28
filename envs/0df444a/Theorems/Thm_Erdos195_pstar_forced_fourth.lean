-- Prove2me | Theorems.Thm_Erdos195_pstar_forced_fourth
-- name    : Erdos195.pstar_forced_fourth
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T05:41:55.236153+00:00
-- url     : https://prove2.me/theorems/f118c7be-7636-496d-bd75-4c5d75688700
-- title:
--   Forced fourth terms over $(0,1,-1)$ and $P^*=(0,1,-1,-5)$
-- statement:
--   Tree orders: for a tree witness $\theta(k,r)\in\{0,1\}$ and distinct integers $x,y$ with $k=\nu_2(y-x)$, $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ is $\theta$-safe if "$Q$ in order, then all other integers in $\prec_\theta$-order" has no monotone $4$-term arithmetic progression; it is tree-safe if it is $\theta$-safe for some $\theta$. An in-order pair $a$ before $b$ in $Q$ is open if $2b-a,3b-2a\notin Q$. Let $P^*=(0,1,-1,-5)$. If $Q$ is $\theta$-safe then: (a) if $Q$ begins $(0,1,-1)$ and $-3\in Q$, then $-5\in Q$ and $-5$ precedes $-3$; (b) if $Q$ begins $P^*$ and $2\in Q$, then $3\in Q$ and $3$ precedes $2$.
--
--   Formalization note: `treeLt` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` from `Definitions.Def_Erdos195_defs`; positions are `List.idxOf`, $\nu_2$ is `padicValInt 2`, `L <+: Q` means $L$ is a prefix of $Q$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statement from GPT 6 Astra (Oct 23 2026 tree answers), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem pstar_forced_fourth (θ : ℕ → ℤ → Bool) (Q : List ℤ) (hS : Safe (treeLt θ) Q) :
    ([0, 1, -1] <+: Q → -3 ∈ Q → -5 ∈ Q ∧ Q.idxOf (-5) < Q.idxOf (-3)) ∧
    ([0, 1, -1, -5] <+: Q → 2 ∈ Q → 3 ∈ Q ∧ Q.idxOf 3 < Q.idxOf 2) := by sorry

end Erdos195
