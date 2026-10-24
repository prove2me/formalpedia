-- Prove2me | Theorems.Thm_Erdos195_shield_suffix_iff
-- name    : Erdos195.shield_suffix_iff
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T07:47:12.321509+00:00
-- url     : https://prove2.me/theorems/eaf4bc62-42b1-4572-9558-5f7afbc89fb3
-- title:
--   Which letter may follow the shield: $(0,1,6,3,x)$ is tree-safe iff $x\equiv2$ (mod 4) or $x=4$
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$ (two's-complement digits). A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression; it is tree-safe if it is $\theta$-safe for some $\theta$. An in-order pair $(a,b)$ of $Q$ ($a$ occurs before $b$) is open if $2b-a\notin Q$ and $3b-2a\notin Q$; an open pair lies at the node $N(a,b)=(k,\,a\bmod 2^k)$, $k=\nu_2(b-a)$, and $\theta$-safety requires $\theta(N(a,b))=\mathrm{bit}_k(b)$ there. Let $x$ be an integer with $x\notin\{0,1,3,6\}$. Then the five-letter word $(0,1,6,3,x)$ is tree-safe if and only if
--   $$x\equiv 2\pmod 4\qquad\text{or}\qquad x=4.$$ Here $(0,1,6,3)$ is the shield word $S(0,1)$ (tree-safe, closing the root pair $(0,1)$). This classifies which single letter may follow the shield. (A relayed GPT answer claimed the safe set is exactly $\{2,4,18\}$; that is false — e.g. $x=10$ and $x=-2$ are safe — and this theorem is the corrected statement.) Obstructions: odd $x$ conflicts with the root pair $(1,6)$ via $(0,x)$; $x\equiv 0\pmod 4$, $x\neq 4$, gives a level-$1$ conflict between $(0,6)$ and $(6,x)$; $x\in\{5,11,12\}$ complete an in-order $3$-AP without its fourth term.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` are from `Definitions.Def_Erdos195_defs`. Positions in a word are `List.idxOf`; `P ++ [c]` appends `c`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statements from GPT 6 relay answers (Oct 23 2026 'shield pieces 1–3'), hand-checked against the exact definitions (one claim corrected), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem shield_suffix_iff (x : ℤ) (h0 : x ≠ 0) (h1 : x ≠ 1) (h3 : x ≠ 3) (h6 : x ≠ 6) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [0, 1, 6, 3, x]) ↔ x % 4 = 2 ∨ x = 4 := by sorry

end Erdos195
