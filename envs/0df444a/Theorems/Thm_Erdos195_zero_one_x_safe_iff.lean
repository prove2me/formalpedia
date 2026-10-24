-- Prove2me | Theorems.Thm_Erdos195_zero_one_x_safe_iff
-- name    : Erdos195.zero_one_x_safe_iff
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T07:47:07.41041+00:00
-- url     : https://prove2.me/theorems/52359d7c-db31-4e28-80b5-6d83438de6f0
-- title:
--   $(0,1,x)$ is tree-safe iff $x$ is odd
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$ (two's-complement digits). A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression; it is tree-safe if it is $\theta$-safe for some $\theta$. An in-order pair $(a,b)$ of $Q$ ($a$ occurs before $b$) is open if $2b-a\notin Q$ and $3b-2a\notin Q$; an open pair lies at the node $N(a,b)=(k,\,a\bmod 2^k)$, $k=\nu_2(b-a)$, and $\theta$-safety requires $\theta(N(a,b))=\mathrm{bit}_k(b)$ there. Let $x$ be an integer with $x\notin\{0,1\}$. Then the three-letter word $(0,1,x)$ is tree-safe if and only if
--   $$x \text{ is odd}.$$
--   For even $x$ the open root pair $(0,1)$ conflicts with $(1,x)$ (or, for $x=2$, $(0,1,2)$ is an in-order $3$-AP with no fourth term); for odd $x$ every open pair at the root starts at $0$.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` are from `Definitions.Def_Erdos195_defs`. Positions in a word are `List.idxOf`; `P ++ [c]` appends `c`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statements from GPT 6 relay answers (Oct 23 2026 'shield pieces 1–3'), hand-checked against the exact definitions (one claim corrected), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem zero_one_x_safe_iff (x : ℤ) (h0 : x ≠ 0) (h1 : x ≠ 1) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [0, 1, x]) ↔ x % 2 = 1 := by sorry

end Erdos195
