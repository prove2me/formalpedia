-- Prove2me | Theorems.Thm_CannonFloydParry_two_pow_le_encard_wordBall
-- name    : CannonFloydParry.two_pow_le_encard_wordBall
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-17T12:05:04.201414+00:00
-- url     : https://prove2.me/theorems/a3374e25-d9cd-4208-ad7f-1e143d30b21e
-- title:
--   Corollary 4.7: $F$ has exponential growth
-- statement:
--   For every $n$, the set of elements of $\operatorname{Aut}[0,1]$ that can be written as a
--   product of at most $n$ factors, each factor one of $A$, $B$, $A^{-1}$, $B^{-1}$, has cardinality
--   at least $2^n$ (cardinality taken in $\mathbb{N}\cup\{\infty\}$, so the inequality is meaningful
--   without a separate finiteness claim).
--
--   This is the source's corollary in concrete form. "Exponential growth" of a finitely generated
--   group means that the ball of radius $n$ in the word metric of some (equivalently, any) finite
--   generating set has at least $c^n$ elements for some $c > 1$; $\{A, B\}$ generates $F$
--   (Corollary 2.6), the ball is the set above, and the statement gives $c = 2$. The growth
--   function itself and its independence of the generating set are not formalized.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, Corollary 4.7, p. 231.

import Definitions.Def_CannonFloydParry
import Mathlib

namespace CannonFloydParry

/-- Corollary 4.7, in concrete form.  With respect to the generators `A`, `B` of `F`, the ball
of radius `n` — the elements that are products of at most `n` factors, each one of `A`, `B`,
`A⁻¹`, `B⁻¹` — has at least `2 ^ n` elements.  So `F` has exponential growth. -/
theorem two_pow_le_encard_wordBall (n : ℕ) :
    (2 : ℕ∞) ^ n ≤
      Set.encard {g : UI ≃o UI | ∃ l : List (UI ≃o UI), l.length ≤ n ∧
        (∀ x ∈ l, x = mapA ∨ x = mapB ∨ x = mapA⁻¹ ∨ x = mapB⁻¹) ∧ l.prod = g} := by
  sorry

end CannonFloydParry
