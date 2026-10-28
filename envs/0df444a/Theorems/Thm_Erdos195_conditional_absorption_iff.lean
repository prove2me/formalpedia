-- Prove2me | Theorems.Thm_Erdos195_conditional_absorption_iff
-- name    : Erdos195.conditional_absorption_iff
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T06:37:52.503034+00:00
-- url     : https://prove2.me/theorems/e8c190e4-be08-49ca-9f5b-109486d44d97
-- title:
--   Fixed-witness one-letter absorption criterion for tree-safe words
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$ (two's-complement digits). A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression; it is tree-safe if it is $\theta$-safe for some $\theta$. An in-order pair $(a,b)$ of $Q$ ($a$ occurs before $b$) is open if $2b-a\notin Q$ and $3b-2a\notin Q$; an open pair lies at the node $N(a,b)=(k,\,a\bmod 2^k)$, $k=\nu_2(b-a)$, and $\theta$-safety requires $\theta(N(a,b))=\mathrm{bit}_k(b)$ there. Let $R$ be a $\theta$-safe word and $t\notin R$. Then $R\cdot t$ is $\theta$-safe (for the same $\theta$) if and only if
--   $$\text{(i) } t=2b-a \text{ for an in-order pair } (a,b) \text{ of } R \implies 3b-2a\in R,\qquad \text{(ii) } x\in R,\ x\prec_\theta t \implies 2t-x\in R \text{ or } 3t-2x\in R.$$
--   In particular (Astra's conditional absorption) if $t$ is not a third term of any in-order $3$-AP of $R$ and every letter $x\prec_\theta t$ of $R$ already has $2t-x$ or $3t-2x$ in $R$, then $t$ can be appended without changing the witness. This is the fixed-witness one-letter extension criterion; it contains bottom insertion (all letters $\succ_\theta t$) as the special case where (ii) is vacuous (Erdős Problem 195).
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` are from `Definitions.Def_Erdos195_defs`. Positions in a word are `List.idxOf`; `P ++ [c]` appends `c`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statements from GPT 6 Astra (Oct 23 2026 'tree11' answer, checked and sharpened), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem conditional_absorption_iff (θ : ℕ → ℤ → Bool) (R : List ℤ) (t : ℤ)
    (hR : Safe (treeLt θ) R) (ht : t ∉ R) :
    Safe (treeLt θ) (R ++ [t]) ↔
      (∀ a b : ℤ, a ∈ R → b ∈ R → R.idxOf a < R.idxOf b → t = 2 * b - a → 3 * b - 2 * a ∈ R) ∧
      (∀ x ∈ R, treeLt θ x t → 2 * t - x ∈ R ∨ 3 * t - 2 * x ∈ R) := by sorry

end Erdos195
