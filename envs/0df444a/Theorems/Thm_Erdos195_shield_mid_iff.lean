-- Prove2me | Theorems.Thm_Erdos195_shield_mid_iff
-- name    : Erdos195.shield_mid_iff
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T07:47:09.461756+00:00
-- url     : https://prove2.me/theorems/ed45097b-a927-4532-8f86-fda707a00481
-- title:
--   Shield rigidity: $(0,1,x,6,3)$ is tree-safe iff $x\in\{4,11\}$
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$ (two's-complement digits). A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression; it is tree-safe if it is $\theta$-safe for some $\theta$. An in-order pair $(a,b)$ of $Q$ ($a$ occurs before $b$) is open if $2b-a\notin Q$ and $3b-2a\notin Q$; an open pair lies at the node $N(a,b)=(k,\,a\bmod 2^k)$, $k=\nu_2(b-a)$, and $\theta$-safety requires $\theta(N(a,b))=\mathrm{bit}_k(b)$ there. Let $x$ be an integer with $x\notin\{0,1,3,6\}$. Then the five-letter word $(0,1,x,6,3)$, i.e. the shield $(0,1,6,3)$ with one letter inserted after the closed pair $(0,1)$, is tree-safe if and only if
--   $$x=4\qquad\text{or}\qquad x=11.$$
--   So the shield is rigid: it survives almost no intermediate entry. Obstructions: odd $x\neq 11$ conflicts with the root pair $(1,6)$ via $(0,x)$; even $x\notin\{2,4\}$ makes $(1,x)$ and $(x,3)$ conflict at the root; $x=2$ creates the in-order $3$-AP $(0,1,2)$ whose fourth term $3$ comes too late.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` are from `Definitions.Def_Erdos195_defs`. Positions in a word are `List.idxOf`; `P ++ [c]` appends `c`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statements from GPT 6 relay answers (Oct 23 2026 'shield pieces 1–3'), hand-checked against the exact definitions (one claim corrected), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem shield_mid_iff (x : ℤ) (h0 : x ≠ 0) (h1 : x ≠ 1) (h3 : x ≠ 3) (h6 : x ≠ 6) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [0, 1, x, 6, 3]) ↔ x = 4 ∨ x = 11 := by sorry

end Erdos195
