-- Prove2me | Theorems.Thm_Erdos195_escape_chain_terminates
-- name    : Erdos195.escape_chain_terminates
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T21:19:16.229953+00:00
-- url     : https://prove2.me/theorems/792f0191-afcd-4970-89e5-de4d9fc0192a
-- title:
--   Escape chains terminate: o + 3^n(w−o) ends in a reflection or precedes o (root bit 1)
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$ (milestone framework); it satisfies Ho's identity $(*)$: $x\prec x+r \iff x+2r\prec x+3r$. A finite word $Q$ of integers is $\theta$-safe if the sequence "letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression; positions are first occurrences. With root bit $\theta(0,0)=1$, every odd $o$ before an even $v$ is either reflected ($2v-o$ occurs before $v$) or escapes ($3v-2o$ occurs). The escape $3v-2o$ is again even.
--
--   **Theorem (escape chains terminate).** Let $\theta(0,0)=1$, let $Q$ be $\theta$-safe, and let $o$ odd come before $w$ even in $Q$. Put $e_m=o+3^m(w-o)$, so $e_0=w$ and $e_{m+1}=3e_m-2o$ is the escape of $o$ at $e_m$. Then there is $n\ge 0$ such that $e_0,\dots,e_n\in Q$, $o$ comes before each of $e_0,\dots,e_{n-1}$, and either
--   (i) $o$ comes before $e_n$ and $2e_n-o\in Q$ comes before $e_n$ (a genuine reflection), or
--   (ii) $n>0$ and $e_n$ comes before $o$.
--
--   So escapes cannot be used indefinitely. Each inverted (odd, even) pair starts a geometric chain of escapes with ratio 3 about $o$, and the chain must end in a reflection or in a letter placed before $o$. In particular, if no even letter precedes $o$, some $e_n$ is genuinely reflected. This is a structural lemma for Erdős #195, not a construction or an impossibility result.
--
--   Formalization note: words are `List ℤ`, positions via `List.idxOf`, safety is `Safe (treeLt θ)`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem escape_chain_terminates (θ : ℕ → ℤ → Bool) (h00 : θ 0 0 = true) (Q : List ℤ)
    (hS : Safe (treeLt θ) Q) (o w : ℤ) (ho : o ∈ Q) (hw : w ∈ Q) (hoo : o % 2 = 1)
    (hwe : w % 2 = 0) (hi : Q.idxOf o < Q.idxOf w) :
    ∃ n : ℕ, (∀ m ≤ n, o + 3 ^ m * (w - o) ∈ Q) ∧
      (∀ m < n, Q.idxOf o < Q.idxOf (o + 3 ^ m * (w - o))) ∧
      ((Q.idxOf o < Q.idxOf (o + 3 ^ n * (w - o)) ∧
          2 * (o + 3 ^ n * (w - o)) - o ∈ Q ∧
          Q.idxOf (2 * (o + 3 ^ n * (w - o)) - o) < Q.idxOf (o + 3 ^ n * (w - o))) ∨
        (0 < n ∧ Q.idxOf (o + 3 ^ n * (w - o)) < Q.idxOf o)) := by sorry

end Erdos195
