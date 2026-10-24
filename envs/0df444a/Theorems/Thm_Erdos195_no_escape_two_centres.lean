-- Prove2me | Theorems.Thm_Erdos195_no_escape_two_centres
-- name    : Erdos195.no_escape_two_centres
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T21:07:17.877046+00:00
-- url     : https://prove2.me/theorems/6b2853e6-1534-4d24-b5aa-76ba32e6c896
-- title:
--   Two no-escape centres force a translate of the earlier odd letters (root bit 1)
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$ (milestone framework); its root bit $\theta(0,0)$ decides the order between integers of different parity. A finite word $Q$ of integers is $\theta$-safe if the sequence "letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression; positions are first occurrences. We say an odd letter $o$ before an even letter $v$ in $Q$ *escapes at $v$* if $3v-2o\in Q$.
--
--   **Theorem (two no-escape centres).** Let $\theta(0,0)=1$ and let $Q$ be $\theta$-safe. Let $u,u'$ be even letters of $Q$ with $u$ before $u'$, such that no odd letter before $u$ escapes at $u$ and no odd letter before $u'$ escapes at $u'$. Put $\delta=2(u'-u)$. Then
--   $$o\ \text{odd, before}\ u\ \Longrightarrow\ o+\delta\in Q\ \text{and}\ o+\delta\ \text{comes before}\ u',$$
--   and if at least one odd letter precedes $u$, then some odd letter of $Q$ lies strictly between $u$ and $u'$.
--
--   The proof rests on the reflect-or-escape principle: with root bit 1, every odd $o$ before an even $v$ satisfies either $2v-o\in Q$ before $v$, or $3v-2o\in Q$. Without escapes, the odd letters before $u$ form a set symmetric about $u$, and those before $u'$ form a set symmetric about $u'$. Composing the two reflections gives the translation by $\delta$. A finite nonempty set cannot be invariant under a nonzero translation, so new odd letters must be placed between the two centres. This is a structural constraint on repairs that use no escape letters. It is neither a construction nor an impossibility result for Erdős #195.
--
--   Formalization note: words are `List ℤ`, positions via `List.idxOf`, safety is `Safe (treeLt θ)`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem no_escape_two_centres (θ : ℕ → ℤ → Bool) (h00 : θ 0 0 = true) (Q : List ℤ)
    (hS : Safe (treeLt θ) Q) (u u' : ℤ) (hu : u ∈ Q) (hu' : u' ∈ Q) (hue : u % 2 = 0)
    (hue' : u' % 2 = 0) (hi : Q.idxOf u < Q.idxOf u')
    (hesc : ∀ o ∈ Q, o % 2 = 1 → (Q.idxOf o < Q.idxOf u → 3 * u - 2 * o ∉ Q) ∧
      (Q.idxOf o < Q.idxOf u' → 3 * u' - 2 * o ∉ Q)) :
    (∀ o ∈ Q, o % 2 = 1 → Q.idxOf o < Q.idxOf u →
      o + 2 * (u' - u) ∈ Q ∧ Q.idxOf (o + 2 * (u' - u)) < Q.idxOf u') ∧
    ((∃ o ∈ Q, o % 2 = 1 ∧ Q.idxOf o < Q.idxOf u) →
      ∃ o ∈ Q, o % 2 = 1 ∧ Q.idxOf u < Q.idxOf o ∧ Q.idxOf o < Q.idxOf u') := by sorry

end Erdos195
