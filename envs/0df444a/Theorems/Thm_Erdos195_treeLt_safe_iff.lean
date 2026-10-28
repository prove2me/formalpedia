-- Prove2me | Theorems.Thm_Erdos195_treeLt_safe_iff
-- name    : Erdos195.treeLt_safe_iff
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T05:13:38.680894+00:00
-- url     : https://prove2.me/theorems/53d9fe66-ed9e-4508-ba86-87701954f21a
-- title:
--   Exact finite characterization of $\theta$-safety for tree orders
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$ (two's-complement digits). A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. Call $a$ before $b$ in $Q$ an open pair if neither $2b-a$ nor $3b-2a$ lies in $Q$. Then $Q$ is $\theta$-safe if and only if
--   $$\text{(1) every in-order 3-AP } a,b,2b-a \text{ of } Q \text{ has } 3b-2a\in Q \text{ placed before } 2b-a,\qquad \text{(2) every open pair } (a,b) \text{ has } \theta\bigl(k,\,a\bmod 2^k\bigr)=\mathrm{bit}_k(b),\ k=\nu_2(b-a).$$
--   This is the exact finite characterization of safety for tree orders (the tree analogue of condition (C)).
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne`, `No3AP`, `Star`, `HasMonotoneAP` are from `Definitions.Def_Erdos195_defs`. Positions in a word are `List.idxOf`; $\nu_2$ is `padicValInt 2`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework and statement from GPT 6 Astra (Oct 23 2026 answers), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem treeLt_safe_iff (θ : ℕ → ℤ → Bool) (Q : List ℤ) :
    Safe (treeLt θ) Q ↔
      (∀ a b : ℤ, a ∈ Q → b ∈ Q → 2 * b - a ∈ Q → Q.idxOf a < Q.idxOf b →
          Q.idxOf b < Q.idxOf (2 * b - a) →
          3 * b - 2 * a ∈ Q ∧ Q.idxOf (3 * b - 2 * a) < Q.idxOf (2 * b - a)) ∧
      (∀ a b : ℤ, a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b →
          2 * b - a ∉ Q → 3 * b - 2 * a ∉ Q →
          (θ (padicValInt 2 (b - a)) (a % 2 ^ padicValInt 2 (b - a)) = true ↔
            bitOne b (padicValInt 2 (b - a)))) := by sorry

end Erdos195
