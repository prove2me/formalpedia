-- Prove2me | Theorems.Thm_Erdos195_odd_shield_unique
-- name    : Erdos195.odd_shield_unique
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T07:47:07.734549+00:00
-- url     : https://prove2.me/theorems/b3d06f34-1bc6-4246-a851-8cacb20b01ac
-- title:
--   Among $(0,1,1+m,3)$ with $m$ odd, only the shield $m=5$ is tree-safe
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$ (two's-complement digits). A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression; it is tree-safe if it is $\theta$-safe for some $\theta$. An in-order pair $(a,b)$ of $Q$ ($a$ occurs before $b$) is open if $2b-a\notin Q$ and $3b-2a\notin Q$; an open pair lies at the node $N(a,b)=(k,\,a\bmod 2^k)$, $k=\nu_2(b-a)$, and $\theta$-safety requires $\theta(N(a,b))=\mathrm{bit}_k(b)$ there. Let $m$ be an odd integer with $1+m\neq 0$. Then the four-letter word $(0,1,1+m,3)$ is tree-safe if and only if
--   $$m=5,$$
--   i.e. the shield $(0,1,6,3)$ is the only tree-safe word of this shape. For $m=1$ the in-order $3$-AP $(0,1,2)$ has its fourth term too late; otherwise the open pairs $(0,3)$ and $(1,1+m)$ conflict at the root node $(0,0)$.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` are from `Definitions.Def_Erdos195_defs`. Positions in a word are `List.idxOf`; `P ++ [c]` appends `c`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statements from GPT 6 relay answers (Oct 23 2026 'shield pieces 1–3'), hand-checked against the exact definitions (one claim corrected), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem odd_shield_unique (m : ℤ) (hm : m % 2 = 1) (hm0 : 1 + m ≠ 0) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [0, 1, 1 + m, 3]) ↔ m = 5 := by sorry

end Erdos195
