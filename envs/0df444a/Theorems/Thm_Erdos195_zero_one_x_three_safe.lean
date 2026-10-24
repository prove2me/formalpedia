-- Prove2me | Theorems.Thm_Erdos195_zero_one_x_three_safe
-- name    : Erdos195.zero_one_x_three_safe
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T07:47:16.739809+00:00
-- url     : https://prove2.me/theorems/158b3382-ad06-40d5-9b19-620bfaeb8285
-- title:
--   $(0,1,x,3)$ is tree-safe for every odd $x\notin\{1,3\}$
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$ (two's-complement digits). A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression; it is tree-safe if it is $\theta$-safe for some $\theta$. An in-order pair $(a,b)$ of $Q$ ($a$ occurs before $b$) is open if $2b-a\notin Q$ and $3b-2a\notin Q$; an open pair lies at the node $N(a,b)=(k,\,a\bmod 2^k)$, $k=\nu_2(b-a)$, and $\theta$-safety requires $\theta(N(a,b))=\mathrm{bit}_k(b)$ there. Let $x$ be an odd integer with $x\notin\{1,3\}$. Then the word $(0,1,x,3)$ is tree-safe; moreover $(0,1,3)$ is tree-safe.
--   $$x \text{ odd},\ x\neq 1,3\ \Longrightarrow\ (0,1,x,3)\ \text{is tree-safe}.$$
--   Appending $3=3\cdot 1-2\cdot 0$ closes the root pair $(0,1)$ after any odd entry. This does not release the root node: the open pairs $(0,x)$ and (unless $x=9$) $(0,3)$ still force $\theta(0,0)=1$.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` are from `Definitions.Def_Erdos195_defs`. Positions in a word are `List.idxOf`; `P ++ [c]` appends `c`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statements from GPT 6 relay answers (Oct 23 2026 'shield pieces 1–3'), hand-checked against the exact definitions (one claim corrected), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem zero_one_x_three_safe (x : ℤ) (hx : x % 2 = 1) (h1 : x ≠ 1) (h3 : x ≠ 3) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [0, 1, x, 3]) ∧
      (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [0, 1, 3]) := by sorry

end Erdos195
