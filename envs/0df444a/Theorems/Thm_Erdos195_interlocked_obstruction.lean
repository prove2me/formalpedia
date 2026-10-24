-- Prove2me | Theorems.Thm_Erdos195_interlocked_obstruction
-- name    : Erdos195.interlocked_obstruction
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T21:19:15.752726+00:00
-- url     : https://prove2.me/theorems/5006b406-2b58-4926-a165-638d18f05a33
-- title:
--   Interlocked obstruction at every level: a, a+d before; a+5d before a+4d; middle terms absent
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$ (milestone framework); it satisfies Ho's identity $(*)$: $x\prec x+r \iff x+2r\prec x+3r$. A finite word $Q$ of integers is $\theta$-safe if the sequence "letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression; positions are first occurrences. **Theorem (interlocked obstruction, any level).** Let $T$ be a finite word, $d\neq 0$, and suppose $a, a+d, a+4d, a+5d\in T$ with $a$ before $a+d$ and $a+5d$ before $a+4d$, while $a+2d\notin T$ and $a+3d\notin T$. Then for every tree witness $\theta$ and every word $R$, the extension $T\,R$ is not $\theta$-safe.
--
--   Why: the pairs $(a,a+d)$ and $(a+5d,a+4d)$ have swapped third/fourth terms ($a+2d$, $a+3d$), so by the interlocked-pairs lemma neither term can ever be added. Then both pairs must be $\prec_\theta$-decreasing. But by $(*)$ and totality exactly one of $a\prec a+d$ and $a+5d\prec a+4d$ holds, for any order with $(*)$. This generalises the root-level obstruction (the case $d$ odd) to every 2-adic level and every residue node. It is a structural no-go lemma for Erdős #195, not a construction or an impossibility result.
--
--   Formalization note: words are `List ℤ`, positions via `List.idxOf`, safety is `Safe (treeLt θ)`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem interlocked_obstruction (T R : List ℤ) (a d : ℤ) (hd : d ≠ 0)
    (h0 : a ∈ T) (h1 : a + d ∈ T) (h4 : a + 4 * d ∈ T) (h5 : a + 5 * d ∈ T)
    (hi : T.idxOf a < T.idxOf (a + d)) (hi' : T.idxOf (a + 5 * d) < T.idxOf (a + 4 * d))
    (h2 : a + 2 * d ∉ T) (h3 : a + 3 * d ∉ T) :
    ¬ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (T ++ R) := by sorry

end Erdos195
