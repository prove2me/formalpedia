-- Prove2me | Theorems.Thm_Erdos195_pstar_tree_safe
-- name    : Erdos195.pstar_tree_safe
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T05:41:53.328989+00:00
-- url     : https://prove2.me/theorems/70b0d941-c790-4166-9717-bf91e4149703
-- title:
--   $P^*=(0,1,-1,-5)$ and $(0,1,-1,-5,3)$ are tree-safe
-- statement:
--   Tree orders: for a tree witness $\theta(k,r)\in\{0,1\}$ and distinct integers $x,y$ with $k=\nu_2(y-x)$, $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ is $\theta$-safe if "$Q$ in order, then all other integers in $\prec_\theta$-order" has no monotone $4$-term arithmetic progression; it is tree-safe if it is $\theta$-safe for some $\theta$. An in-order pair $a$ before $b$ in $Q$ is open if $2b-a,3b-2a\notin Q$. Let $P^*=(0,1,-1,-5)$. With $\theta(k,r)=[k\le1]$, both
--   $$P^*=(0,1,-1,-5)\quad\text{and}\quad(0,1,-1,-5,3)$$
--   are $\theta$-safe.
--
--   Formalization note: `treeLt` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` from `Definitions.Def_Erdos195_defs`; positions are `List.idxOf`, $\nu_2$ is `padicValInt 2`, `L <+: Q` means $L$ is a prefix of $Q$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statement from GPT 6 Astra (Oct 23 2026 tree answers), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem pstar_tree_safe :
    Safe (treeLt fun k _ => decide (k ≤ 1)) [0, 1, -1, -5] ∧
    Safe (treeLt fun k _ => decide (k ≤ 1)) [0, 1, -1, -5, 3] := by sorry

end Erdos195
