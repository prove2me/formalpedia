-- Prove2me | Theorems.Thm_Erdos195_no_isolated_max_analogue
-- name    : Erdos195.no_isolated_max_analogue
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T06:12:29.820259+00:00
-- url     : https://prove2.me/theorems/7b93ff2b-6adb-4ff7-a116-2cc6cc06ee9b
-- title:
--   The isolated-minimum completion has no isolated-maximum analogue
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$ (two's-complement digits). A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression; it is tree-safe if it is $\theta$-safe for some $\theta$. The isolated-minimum completion (if $b$ is the $\theta$-minimum of a $\theta$-safe word $P$, alone in its class mod $2^{\nu_2(b-a)+1}$, and $3b-2a$ is not a third term $2v-u$ of an in-order pair, then $P\cdot(3b-2a)$ is tree-safe) has no maximum analogue: there exist $\theta$, $P$, $a\neq b$ with $P$ $\theta$-safe, $b\in P$ the $\theta$-maximum of $P$, $b$ alone in its class mod $2^{\nu_2(b-a)+1}$, and $3b-2a\neq 2v-u$ for all in-order pairs $(u,v)$ of $P$, such that
--   $$P\cdot(3b-2a)\ \text{is not tree-safe}.$$
--   A witness is $\theta\equiv1$, $P=(0,1)$, $a=1$, $b=0$: the pairs $(0,1)$ and $(1,-2)$ force opposite values at the root (Erdős Problem 195).
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` are from `Definitions.Def_Erdos195_defs`. Positions in a word are `List.idxOf`; `P ++ [c]` appends `c`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statements from GPT 6 Astra (Oct 23 2026 'tree' answers tree10, generalized), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem no_isolated_max_analogue :
    ∃ (θ : ℕ → ℤ → Bool) (P : List ℤ) (a b : ℤ),
      Safe (treeLt θ) P ∧ b ∈ P ∧ a ≠ b ∧
      (∀ x ∈ P, x ≠ b → treeLt θ x b) ∧
      (∀ x ∈ P, x ≠ b → ¬ (2 : ℤ) ^ (padicValInt 2 (b - a) + 1) ∣ x - b) ∧
      (∀ u v : ℤ, u ∈ P → v ∈ P → P.idxOf u < P.idxOf v → 3 * b - 2 * a ≠ 2 * v - u) ∧
      ¬ ∃ θ' : ℕ → ℤ → Bool, Safe (treeLt θ') (P ++ [3 * b - 2 * a]) := by sorry

end Erdos195
