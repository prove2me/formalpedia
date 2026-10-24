-- Prove2me | Theorems.Thm_Erdos195_W16_safe_released
-- name    : Erdos195.W16_safe_released
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T09:56:53.46507+00:00
-- url     : https://prove2.me/theorems/6d256000-db8c-4c1d-8620-30ef06d06a37
-- title:
--   The word $W_{16}$ is a tree-safe true root release
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. An in-order pair $(a,b)$ of $Q$ ($a$ occurs before $b$) is open if $2b-a\notin Q$ and $3b-2a\notin Q$; it lies at the node $(k,\,a\bmod 2^k)$, $k=\nu_2(b-a)$, and forces $\theta$ there to equal $\mathrm{bit}_k(b)$. A root pair is one with $b-a$ odd (node $(0,0)$); $Q$ is a true root release if every open root pair has even second entry, i.e. no open pair forces the value $1$ at the root. The $32$-letter word $W_{16}$ is $\theta$-safe for some tree witness and is a true root release. It consists of $0$; the even powers $3^{2t}$, $t=0,\dots,14$, in the order $t=0,8,4,12,2,10,6,14,1,9,5,13,3,11,7$; the odd powers $3^{2t+1}$ in the order $t=13,5,9,1,11,3,7,12,4,8,0,10,2,6$; then $2\cdot3^{29}$ and $3^{29}$. This is the case $j=16$ of the bit-reversal family $W_j$.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` are from `Definitions.Def_Erdos195_defs`. Positions are `List.idxOf`; the release property is stated as: every open in-order pair $(a,b)$ with $(b-a) \bmod 2 = 1$ has $b \bmod 2 = 0$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; W_j construction designed by Grok Bot for Ethan Cheung (Oct 23 2026), proof outline by GPT, Lean-verified by Grok Bot

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem W16_safe_released :
    let Q : List ℤ := [0, 1, 43046721, 6561, 282429536481, 81, 3486784401, 531441, 22876792454961, 9, 387420489, 59049, 2541865828329, 729, 31381059609, 4782969, 7625597484987, 177147, 1162261467, 27, 94143178827, 2187, 14348907, 847288609443, 19683, 129140163, 3, 10460353203, 243, 1594323, 137260754729766, 68630377364883]
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) Q) ∧
    ∀ a b : ℤ, a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b → 2 * b - a ∉ Q → 3 * b - 2 * a ∉ Q →
      (b - a) % 2 = 1 → b % 2 = 0 := by sorry

end Erdos195
