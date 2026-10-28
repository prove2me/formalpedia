-- Prove2me | Theorems.Thm_Erdos195_tree_append_iff
-- name    : Erdos195.tree_append_iff
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T05:15:30.460305+00:00
-- url     : https://prove2.me/theorems/f07e946e-b977-4fa8-91d2-3edfca3825f5
-- title:
--   Tree append criterion: when $P\cdot t$ is tree-safe
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$ (two's-complement digits). A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. Let $P$ be a word that is $\theta$-safe for some tree witness, and $t\notin P$. Then $P\cdot t$ is $\theta'$-safe for some tree witness $\theta'$ if and only if
--   $$\text{(1) } a \text{ before } b \text{ in } P,\ t=2b-a\ \Rightarrow\ 3b-2a\in P;$$
--   $$\text{(2) for every } x\in P \text{ with } 2t-x,3t-2x\notin P \text{ and every open pair } (a,b) \text{ of } P \text{ (}2b-a,3b-2a\notin P\text{) with } t\notin\{2b-a,3b-2a\},\ \nu_2(b-a)=\nu_2(t-x)=k,\ a\equiv x\ (\mathrm{mod}\ 2^k):\ \mathrm{bit}_k(b)=\mathrm{bit}_k(t).$$
--   So the only possible obstructions to appending $t$ directly are a missing fourth term, and a same-node conflict between a new open pair $(x,t)$ and a surviving old open pair.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne`, `No3AP`, `Star`, `HasMonotoneAP` are from `Definitions.Def_Erdos195_defs`. Positions in a word are `List.idxOf`; $\nu_2$ is `padicValInt 2`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework and statement from GPT 6 Astra (Oct 23 2026 answers), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem tree_append_iff (P : List ℤ) (t : ℤ) (hP : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) P)
    (ht : t ∉ P) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (P ++ [t])) ↔
      (∀ a b : ℤ, a ∈ P → b ∈ P → P.idxOf a < P.idxOf b → t = 2 * b - a → 3 * b - 2 * a ∈ P) ∧
      (∀ x a b : ℤ, x ∈ P → 2 * t - x ∉ P → 3 * t - 2 * x ∉ P →
          a ∈ P → b ∈ P → P.idxOf a < P.idxOf b → 2 * b - a ∉ P → 3 * b - 2 * a ∉ P →
          t ≠ 2 * b - a → t ≠ 3 * b - 2 * a →
          padicValInt 2 (b - a) = padicValInt 2 (t - x) →
          a % 2 ^ padicValInt 2 (b - a) = x % 2 ^ padicValInt 2 (b - a) →
          (bitOne b (padicValInt 2 (b - a)) ↔ bitOne t (padicValInt 2 (b - a)))) := by sorry

end Erdos195
