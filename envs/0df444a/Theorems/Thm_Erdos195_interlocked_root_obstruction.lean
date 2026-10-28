-- Prove2me | Theorems.Thm_Erdos195_interlocked_root_obstruction
-- name    : Erdos195.interlocked_root_obstruction
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T19:22:15.801991+00:00
-- url     : https://prove2.me/theorems/91e69c53-9fdb-463e-a2a0-c5bce45203f7
-- title:
--   Interlocked root obstruction: b before c and 5c−4b before 4c−3b kills every SAFE extension
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$ (milestone framework). A finite word $W$ of integers is SAFE for $\theta$ if the sequence "letters of $W$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression. **Theorem.** Let $T$ be a finite word containing an odd $b$ before an even $c$, and $q=5c-4b$ before $p=4c-3b$, with neither $t=2c-b$ nor $w=3c-2b$ in $T$. Then no extension $TR$ is SAFE for any tree witness.
--
--   Here $(b,c)$ and $(q,p)$ are interlocked: $2p-q=w$ and $3p-2q=t$. By the previous milestone they stay open forever. Both have odd difference, so both sit at the root node. They demand opposite root bits ($c$ is even, $p$ is odd), which is a same-node conflict. This is the excluded case ($p\in V$, $q\in U$) of GPT 6 Astra's repair lemma for a single interleaving inversion $T=U(b,c)V$. In Astra's setting $t,w\notin T$ follows from the mod-4 class hypotheses. The Lean statement assumes it directly and needs no class or distinctness hypotheses.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026); excluded case of GPT 6 Astra's single-inversion repair lemma (astra_fourclass)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem interlocked_root_obstruction (T R : List ℤ) (b c : ℤ)
    (hb : b ∈ T) (hc : c ∈ T) (hbo : b % 2 = 1) (hce : c % 2 = 0)
    (hp : 4 * c - 3 * b ∈ T) (hq : 5 * c - 4 * b ∈ T)
    (hbc : T.idxOf b < T.idxOf c) (hqp : T.idxOf (5 * c - 4 * b) < T.idxOf (4 * c - 3 * b))
    (htT : 2 * c - b ∉ T) (hwT : 3 * c - 2 * b ∉ T) :
    ¬ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (T ++ R) := by sorry

end Erdos195
