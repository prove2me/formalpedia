-- Prove2me | Theorems.Thm_Erdos195_Bt_family_safe_released
-- name    : Erdos195.Bt_family_safe_released
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T11:08:22.810526+00:00
-- url     : https://prove2.me/theorems/fcb03360-214d-4635-bf2b-ee9fd8c61300
-- title:
--   The words $B_t=(0,1,6,3,-8-32t,-2-32t,-1-16t,-70-160t,-78-192t,-36-96t)$ are tree-safe true root releases for all $t\ge0$
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. An in-order pair $(a,b)$ of $Q$ ($a$ occurs before $b$) is open if $2b-a\notin Q$ and $3b-2a\notin Q$; it lies at the node $(k,\,a\bmod 2^k)$, $k=\nu_2(b-a)$, and forces $\theta$ there to equal $\mathrm{bit}_k(b)$. A root pair is one with $b-a$ odd (node $(0,0)$); $Q$ is a true root release if every open root pair has even second entry, i.e. no open pair forces the value $1$ at the root. For every natural number $t$ the word $$B_t=(0,1,6,3,\,-8-32t,\,-2-32t,\,-1-16t,\,-70-160t,\,-78-192t,\,-36-96t)$$ is $\theta$-safe for some tree witness $\theta$ and is a true root release. One witness works for every $t$: $\theta(1,\cdot)=1$, $\theta(2,0)=\theta(2,3)=1$, $\theta(3,0)=\theta(3,6)=1$, and $\theta=0$ everywhere else. All $t$-coefficients are multiples of $16$ and the letters are distinct mod $16$, so every pair meets at level $\le3$, and the nodes and forced bits do not depend on $t$. So the batch can be translated $2$-adically to give an infinite family.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` are from `Definitions.Def_Erdos195_defs`. Positions are `List.idxOf`; the release property is stated as: every open in-order pair $(a,b)$ with $(b-a) \bmod 2 = 1$ has $b \bmod 2 = 0$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; batch words by Sol, Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem Bt_family_safe_released (t : ℕ) :
    let Q : List ℤ := [0, 1, 6, 3, -8 - 32 * (t : ℤ), -2 - 32 * (t : ℤ), -1 - 16 * (t : ℤ),
      -70 - 160 * (t : ℤ), -78 - 192 * (t : ℤ), -36 - 96 * (t : ℤ)]
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) Q) ∧
    ∀ a b : ℤ, a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b → 2 * b - a ∉ Q → 3 * b - 2 * a ∉ Q →
      (b - a) % 2 = 1 → b % 2 = 0 := by sorry

end Erdos195
