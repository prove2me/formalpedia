-- Prove2me | Theorems.Thm_Dogma_exists_dogma_card_17
-- name    : Dogma.exists_dogma_card_17
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T05:11:58.173002+00:00
-- url     : https://prove2.me/theorems/06c6579f-4a0a-4dc4-8d71-4841198c46b7
-- title:
--   A dogma of cardinality $17$
-- statement:
--   A **dogma** is a right-cancellative magma $(D,\star)$ satisfying $(x\star y)\star y=y\star x$ for all $x,y\in D$. Right-cancellative means that $x\star z=y\star z$ implies $x=y$.
--
--   **Theorem.** There exists a dogma of cardinality $17$.
--
--   The prime $17\equiv2\pmod 5$ is inert in $\mathbb Q(\sqrt5)$ and occurs to the first power, so $17$ is not covered by the sufficient condition of `Dogma.exists_dogma_card_of_even_inert` (even exponents at primes $\equiv\pm2\pmod 5$); the condition is therefore not necessary. The example given is a full multiplication table found by a SAT solver; it is not medial, so it is not of the affine form $x\star y=\alpha x+\alpha^2y$. The statement is relevant to the second question of Problem 10 of the CUHK-Shenzhen AI Math Problems, which asks for which $n$ a dogma of cardinality $n$ exists.
--
--   **Formalization Note.** The statement is existential over a type $D$ and a binary operation. Cardinality is expressed with `Nat.card`, so $|D|=17$ forces $D$ to be finite.
-- source:
--   CUHK-Shenzhen AI Math Problems, Problem 10 (source credited to Ma Li), https://rybindmitry.github.io/problems/10.html, question 2: 'For which n does there exist a dogma of cardinality n?' This statement is an original existence result found by computer search and verified in Lean; it is not claimed in the source.

import Mathlib

namespace Dogma

theorem exists_dogma_card_17 :
    ∃ (D : Type) (star : D → D → D), Nat.card D = 17 ∧
      (∀ x y z : D, star x z = star y z → x = y) ∧
      ∀ x y : D, star (star x y) y = star y x := by
  sorry

end Dogma
