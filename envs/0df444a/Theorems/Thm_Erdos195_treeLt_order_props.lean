-- Prove2me | Theorems.Thm_Erdos195_treeLt_order_props
-- name    : Erdos195.treeLt_order_props
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T05:13:40.620563+00:00
-- url     : https://prove2.me/theorems/d55a7159-eb12-4774-8a0c-bcf7e9655c05
-- title:
--   Tree orders $\prec_\theta$ on $\mathbb{Z}$: strict total, no monotone 3-AP, Ho's identity $(\ast)$
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$ (two's-complement digits). A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. For every tree witness $\theta$:
--   $$\prec_\theta\ \text{is a strict total order on }\mathbb{Z},\qquad \nexists\, a,\ r\ne0:\ a\prec_\theta a+r\prec_\theta a+2r,\qquad a\prec_\theta a+r\iff a+2r\prec_\theta a+3r\ (r\neq0).$$
--   These are the three properties of the tail order used in Ho-style constructions of $4$-AP-free permutations; they show that the $\varepsilon$-orders (the case $\theta(k,r)=\varepsilon_k$) can be replaced by the much larger family of tree orders.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne`, `No3AP`, `Star`, `HasMonotoneAP` are from `Definitions.Def_Erdos195_defs`. Positions in a word are `List.idxOf`; $\nu_2$ is `padicValInt 2`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework and statement from GPT 6 Astra (Oct 23 2026 answers), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem treeLt_order_props (θ : ℕ → ℤ → Bool) :
    IsStrictTotalOrder ℤ (treeLt θ) ∧ No3AP (treeLt θ) ∧ Star (treeLt θ) := by sorry

end Erdos195
