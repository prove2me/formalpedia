-- Prove2me | Theorems.Thm_Dogma_exists_dogma_card_1881
-- name    : Dogma.exists_dogma_card_1881
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T03:28:38.841985+00:00
-- url     : https://prove2.me/theorems/0485c611-016a-44a6-8df8-7148a97c8f27
-- title:
--   A dogma of cardinality $1881$
-- statement:
--   A **dogma** is a right-cancellative magma $(D,\star)$ satisfying
--
--   $$
--   (x\star y)\star y \;=\; y\star x \qquad\text{for all }x,y\in D .
--   $$
--
--   Right-cancellative means that $x\star z=y\star z$ implies $x=y$.
--
--   **Theorem.** There exists a dogma of cardinality $1881$.
--
--   This answers the first question of Problem 10 in the CUHK-Shenzhen AI Math Problems (source credited to Ma Li on the problem page): to exhibit a dogma with $1881$ elements. The number $1881=3^2\cdot 11\cdot 19$ is a product of the squared prime $3$, which is inert in $\mathbb Q(\sqrt5)$, and the primes $11$ and $19$, which split in $\mathbb Q(\sqrt5)$.
--
--   **Formalization Note.** The statement is existential over a type $D$ and a binary operation. Cardinality is expressed with `Nat.card`, which is zero for infinite types, so the equation $|D|=1881$ forces $D$ to be finite. Both defining properties are stated for all elements of $D$.
-- source:
--   CUHK-Shenzhen AI Math Problems, Problem 10 (Ma Li), https://rybindmitry.github.io/problems/10.html, question 1: 'Find a dogma of cardinality 1881', where a dogma is a right-cancellative magma with (x*y)*y = y*x (added June 22, 2026).

import Mathlib

namespace Dogma

theorem exists_dogma_card_1881 :
    ∃ (D : Type) (star : D → D → D), Nat.card D = 1881 ∧
      (∀ x y z : D, star x z = star y z → x = y) ∧
      ∀ x y : D, star (star x y) y = star y x := by
  sorry

end Dogma
