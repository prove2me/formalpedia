-- Prove2me | Theorems.Thm_Erdos195_isolated_min_completion
-- name    : Erdos195.isolated_min_completion
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T05:33:34.728735+00:00
-- url     : https://prove2.me/theorems/3b7943ca-0b0e-4a14-8400-64c9260210d6
-- title:
--   Isolated-minimum completion: appending the fourth term $3b-2a$
-- statement:
--   Tree orders: for a tree witness $\theta(k,r)\in\{0,1\}$ and distinct integers $x,y$ with $k=\nu_2(y-x)$, $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ is $\theta$-safe if "$Q$ in order, then all other integers in $\prec_\theta$-order" has no monotone $4$-term arithmetic progression. An in-order pair $a$ before $b$ in $Q$ is open if $2b-a,3b-2a\notin Q$. Let $Q=P$ be $\theta$-safe, $a\ne b$ with $b\in P$, $k=\nu_2(b-a)$, $c=3b-2a$. Suppose $b$ is the $\prec_\theta$-minimum of $P$, $b$ is the only letter of $P$ in its class modulo $2^{k+1}$, and $c\ne 2v-u$ for all $u$ before $v$ in $P$. Let $\theta'$ agree with $\theta$ except at the node $(k+1,\,b\bmod 2^{k+1})$, where $\theta'=\mathrm{bit}_{k+1}(c)$. Then
--   $$P\cdot(3b-2a)\ \text{is}\ \theta'\text{-safe}.$$
--   This is an extremal completion lemma: the fourth term of a pair ending at an isolated minimum can always be appended.
--
--   Formalization note: `treeLt` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` from `Definitions.Def_Erdos195_defs`; positions are `List.idxOf`, $\nu_2$ is `padicValInt 2`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statement from GPT 6 Astra (Oct 23 2026 tree answers), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem isolated_min_completion (θ : ℕ → ℤ → Bool) (P : List ℤ) (a b : ℤ)
    (hP : Safe (treeLt θ) P) (hb : b ∈ P) (hab : a ≠ b)
    (hmin : ∀ x ∈ P, x ≠ b → treeLt θ b x)
    (hiso : ∀ x ∈ P, x ≠ b → ¬ (2 : ℤ) ^ (padicValInt 2 (b - a) + 1) ∣ x - b)
    (hno : ∀ u v : ℤ, u ∈ P → v ∈ P → P.idxOf u < P.idxOf v → 3 * b - 2 * a ≠ 2 * v - u) :
    Safe (treeLt (fun k r => if k = padicValInt 2 (b - a) + 1 ∧ r = b % 2 ^ (padicValInt 2 (b - a) + 1)
        then decide ((3 * b - 2 * a) / 2 ^ (padicValInt 2 (b - a) + 1) % 2 = 1) else θ k r))
      (P ++ [3 * b - 2 * a]) := by sorry

end Erdos195
