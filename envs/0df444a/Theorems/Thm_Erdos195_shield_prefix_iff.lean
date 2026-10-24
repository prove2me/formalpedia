-- Prove2me | Theorems.Thm_Erdos195_shield_prefix_iff
-- name    : Erdos195.shield_prefix_iff
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T07:47:08.9438+00:00
-- url     : https://prove2.me/theorems/638e9fc0-bf9d-447a-b2fe-4c179d63d4ab
-- title:
--   Which letter may precede the shield: $(x,0,1,6,3)$ is tree-safe iff $x\equiv1$ (mod 4) or $x\in\{7,16\}$
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$ (two's-complement digits). A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression; it is tree-safe if it is $\theta$-safe for some $\theta$. An in-order pair $(a,b)$ of $Q$ ($a$ occurs before $b$) is open if $2b-a\notin Q$ and $3b-2a\notin Q$; an open pair lies at the node $N(a,b)=(k,\,a\bmod 2^k)$, $k=\nu_2(b-a)$, and $\theta$-safety requires $\theta(N(a,b))=\mathrm{bit}_k(b)$ there. Let $x$ be an integer with $x\notin\{0,1,3,6\}$. Then the five-letter word $(x,0,1,6,3)$ is tree-safe if and only if
--   $$x\equiv 1 \pmod 4\ \ (x\neq 1),\qquad\text{or}\qquad x=7,\qquad\text{or}\qquad x=16.$$ Here $(0,1,6,3)$ is the shield word $S(0,1)$ (tree-safe, closing the root pair $(0,1)$). The result classifies which single letter may precede the shield. Obstructions: for even $x\neq 16$ the root pair $(1,6)$ (forcing $\mathrm{bit}_0=0$) conflicts at the root with $(x,1)$ or $(x,3)$; for $x\equiv 3\pmod 4$, $x\neq 7$, the pair $(1,3)$ conflicts with $(x,1)$ at level $1$; $x\in\{-1,-4,-6\}$ create an in-order $3$-AP without its fourth term. The exceptions $x=7$, $x=16$ close $(1,3)$ resp. $(1,6)$.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` are from `Definitions.Def_Erdos195_defs`. Positions in a word are `List.idxOf`; `P ++ [c]` appends `c`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statements from GPT 6 relay answers (Oct 23 2026 'shield pieces 1–3'), hand-checked against the exact definitions (one claim corrected), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem shield_prefix_iff (x : ℤ) (h0 : x ≠ 0) (h1 : x ≠ 1) (h3 : x ≠ 3) (h6 : x ≠ 6) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [x, 0, 1, 6, 3]) ↔
      (x % 4 = 1 ∧ x ≠ 1) ∨ x = 7 ∨ x = 16 := by sorry

end Erdos195
