-- Prove2me | Theorems.Thm_Erdos195_two_inversion_translate
-- name    : Erdos195.two_inversion_translate
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T21:07:20.127203+00:00
-- url     : https://prove2.me/theorems/8808c73e-db58-49fe-af94-5e6b4a6b06b5
-- title:
--   Two inverted pairs sharing an odd letter: no-escape repairs force translates of the odd part
-- statement:
--   A tree witness $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ defines a strict total order $\prec_\theta$ on $\mathbb Z$ (milestone framework); its root bit $\theta(0,0)$ decides the order between integers of different parity. A finite word $Q$ of integers is $\theta$-safe if the sequence "letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" has no monotone 4-term arithmetic progression; positions are first occurrences. **Theorem (two inverted pairs sharing the odd letter).** Let $\theta(0,0)=1$. Let $T$ be a word, $b\in T$ odd, and $c\neq c'$ even letters of $T$, both after $b$, such that $t=2c-b$, $w=3c-2b$, $t'=2c'-b$, $w'=3c'-2b$ all lie outside $T$. Let $T\cdot R$ be $\theta$-safe. Suppose that no odd $o$ before $w$ (resp. $w'$) in $T\cdot R$ has $3w-2o\in T\cdot R$ (resp. $3w'-2o\in T\cdot R$). Then $w,w'\in R$. Moreover, if $u$ is the earlier and $u'$ the later of $w,w'$ and $\delta=2(u'-u)$, then
--   $$o\in T\ \text{odd}\ \Longrightarrow\ o+\delta\in T\cdot R\ \text{before}\ u',$$
--   and some odd letter of $R$ lies strictly between $u$ and $u'$.
--
--   The first step is *w-forcing*: with root bit 1, an odd $b$ before an even $c$ with $2c-b,3c-2b\notin T$ forces $3c-2b$ into every safe end-extension. Consequently, a repair of a word with two inversions $(b,c),(b,c')$ that avoids escape letters must contain a translate of the whole odd part of $T$ by $\delta=6(c'-c)$, and these translates come before the later forced letter. So the two-inversion problem does not factor into two independent single-inversion repairs (cf. the single-inversion criterion). It is a structural necessary condition, not a construction or an impossibility result for Erdős #195.
--
--   Formalization note: words are `List ℤ`, positions via `List.idxOf`, safety is `Safe (treeLt θ)`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem two_inversion_translate (θ : ℕ → ℤ → Bool) (h00 : θ 0 0 = true) (T R : List ℤ)
    (hS : Safe (treeLt θ) (T ++ R)) (b c c' : ℤ) (hb : b ∈ T) (hc : c ∈ T) (hc' : c' ∈ T)
    (hbo : b % 2 = 1) (hce : c % 2 = 0) (hce' : c' % 2 = 0) (hcc : c ≠ c')
    (hi : T.idxOf b < T.idxOf c) (hi' : T.idxOf b < T.idxOf c')
    (ht : 2 * c - b ∉ T) (hw : 3 * c - 2 * b ∉ T) (ht' : 2 * c' - b ∉ T) (hw' : 3 * c' - 2 * b ∉ T)
    (hesc : ∀ o ∈ T ++ R, o % 2 = 1 →
      ((T ++ R).idxOf o < (T ++ R).idxOf (3 * c - 2 * b) → 3 * (3 * c - 2 * b) - 2 * o ∉ T ++ R) ∧
      ((T ++ R).idxOf o < (T ++ R).idxOf (3 * c' - 2 * b) → 3 * (3 * c' - 2 * b) - 2 * o ∉ T ++ R)) :
    3 * c - 2 * b ∈ R ∧ 3 * c' - 2 * b ∈ R ∧
    ∃ u u' : ℤ, ((u = 3 * c - 2 * b ∧ u' = 3 * c' - 2 * b) ∨ (u = 3 * c' - 2 * b ∧ u' = 3 * c - 2 * b)) ∧
      (T ++ R).idxOf u < (T ++ R).idxOf u' ∧
      (∀ o ∈ T, o % 2 = 1 → o + 2 * (u' - u) ∈ T ++ R ∧
        (T ++ R).idxOf (o + 2 * (u' - u)) < (T ++ R).idxOf u') ∧
      ∃ o ∈ R, o % 2 = 1 ∧ (T ++ R).idxOf u < (T ++ R).idxOf o ∧ (T ++ R).idxOf o < (T ++ R).idxOf u' := by sorry

end Erdos195
