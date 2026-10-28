-- Prove2me | Theorems.Thm_Erdos195_treeLt_safe_affine
-- name    : Erdos195.treeLt_safe_affine
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T05:13:39.698321+00:00
-- url     : https://prove2.me/theorems/89f94f86-34e1-479b-a5c7-ec14f85c0f77
-- title:
--   Tree-safety is invariant under $x\mapsto ux+v$, $u$ odd
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$ (two's-complement digits). A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. Let $u$ be odd and $v\in\mathbb{Z}$. If $Q$ is $\theta$-safe, then the letterwise image $uQ+v$ is $\theta'$-safe for some tree witness $\theta'$:
--   $$Q\ \theta\text{-safe}\ \Longrightarrow\ \exists\theta':\ (ux_1+v,\dots,ux_n+v)\ \theta'\text{-safe}.$$
--   Thus tree-safety, unlike $\varepsilon$-safety, is invariant under all affine maps $x\mapsto ux+v$ with $u$ odd.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne`, `No3AP`, `Star`, `HasMonotoneAP` are from `Definitions.Def_Erdos195_defs`. Positions in a word are `List.idxOf`; $\nu_2$ is `padicValInt 2`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework and statement from GPT 6 Astra (Oct 23 2026 answers), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem treeLt_safe_affine (u v : ℤ) (hu : Odd u) (θ : ℕ → ℤ → Bool) (Q : List ℤ)
    (h : Safe (treeLt θ) Q) :
    ∃ θ' : ℕ → ℤ → Bool, Safe (treeLt θ') (Q.map (fun x => u * x + v)) := by sorry

end Erdos195
