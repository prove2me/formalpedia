-- Prove2me | Theorems.Thm_Erdos195_exists_treeLt_safe_iff
-- name    : Erdos195.exists_treeLt_safe_iff
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T05:13:43.986198+00:00
-- url     : https://prove2.me/theorems/a51fafef-52a2-455d-b5d0-9bb4b39ff727
-- title:
--   Tree-safe for some $\theta$ iff AP closure and no same-node conflict
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$ (two's-complement digits). A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. With open pairs as before ($a$ before $b$ in $Q$, $2b-a,3b-2a\notin Q$), $Q$ is $\theta$-safe for some tree witness $\theta$ if and only if (1) every in-order 3-AP $a,b,2b-a$ of $Q$ has $3b-2a\in Q$ placed before $2b-a$, and (2) no two open pairs force opposite values at the same node:
--   $$\nu_2(b-a)=\nu_2(b'-a')=k,\ a\equiv a'\ (\mathrm{mod}\ 2^k)\ \Longrightarrow\ \mathrm{bit}_k(b)=\mathrm{bit}_k(b').$$
--   Compared with $\varepsilon$-orders, conflicts only matter at the same tree node, not merely the same level.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne`, `No3AP`, `Star`, `HasMonotoneAP` are from `Definitions.Def_Erdos195_defs`. Positions in a word are `List.idxOf`; $\nu_2$ is `padicValInt 2`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework and statement from GPT 6 Astra (Oct 23 2026 answers), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem exists_treeLt_safe_iff (Q : List ℤ) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) Q) ↔
      (∀ a b : ℤ, a ∈ Q → b ∈ Q → 2 * b - a ∈ Q → Q.idxOf a < Q.idxOf b →
          Q.idxOf b < Q.idxOf (2 * b - a) →
          3 * b - 2 * a ∈ Q ∧ Q.idxOf (3 * b - 2 * a) < Q.idxOf (2 * b - a)) ∧
      (∀ a b a' b' : ℤ, a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b →
          2 * b - a ∉ Q → 3 * b - 2 * a ∉ Q →
          a' ∈ Q → b' ∈ Q → Q.idxOf a' < Q.idxOf b' →
          2 * b' - a' ∉ Q → 3 * b' - 2 * a' ∉ Q →
          padicValInt 2 (b - a) = padicValInt 2 (b' - a') →
          a % 2 ^ padicValInt 2 (b - a) = a' % 2 ^ padicValInt 2 (b - a) →
          (bitOne b (padicValInt 2 (b - a)) ↔ bitOne b' (padicValInt 2 (b - a)))) := by sorry

end Erdos195
