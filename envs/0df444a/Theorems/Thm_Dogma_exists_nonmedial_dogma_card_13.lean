-- Prove2me | Theorems.Thm_Dogma_exists_nonmedial_dogma_card_13
-- name    : Dogma.exists_nonmedial_dogma_card_13
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T04:47:37.898908+00:00
-- url     : https://prove2.me/theorems/ce1aad2e-eec3-4c9a-a3c0-bf0a2bc7a6d7
-- title:
--   A non-medial dogma of cardinality $13$
-- statement:
--   A **dogma** is a right-cancellative magma $(D,\star)$ satisfying $(x\star y)\star y=y\star x$ for all $x,y\in D$. Right-cancellative means that $x\star z=y\star z$ implies $x=y$. A magma is **medial** if $(a\star b)\star(c\star d)=(a\star c)\star(b\star d)$ for all $a,b,c,d$.
--
--   **Theorem.** There exists a dogma of cardinality $13$ which is not medial.
--
--   Dogmas of the form $x\star y=\alpha x+\alpha^2y$ on a commutative ring with $\alpha^2+\alpha=1$ are medial, so this example is of a different kind. The number $13\equiv 3\pmod 5$ is a prime that is inert in $\mathbb Q(\sqrt5)$, so this also shows that the condition of `Dogma.exists_dogma_card_of_even_inert` (even exponents at primes $\equiv\pm2\pmod 5$) is not necessary for the existence of a dogma of a given cardinality. It is relevant to the second question of Problem 10 of the CUHK-Shenzhen AI Math Problems, which asks for which $n$ a dogma of cardinality $n$ exists.
--
--   **Formalization Note.** The statement is existential over a type $D$ and a binary operation. Cardinality is expressed with `Nat.card`, so $|D|=13$ forces $D$ to be finite. The last conjunct exhibits four elements violating mediality.
-- source:
--   CUHK-Shenzhen AI Math Problems, Problem 10 (source credited to Ma Li), https://rybindmitry.github.io/problems/10.html, question 2: 'For which n does there exist a dogma of cardinality n?' This statement is an original existence result found by computer search and verified in Lean; it is not claimed in the source.

import Mathlib

namespace Dogma

theorem exists_nonmedial_dogma_card_13 :
    ∃ (D : Type) (star : D → D → D), Nat.card D = 13 ∧
      (∀ x y z : D, star x z = star y z → x = y) ∧
      (∀ x y : D, star (star x y) y = star y x) ∧
      ∃ a b c d : D, star (star a b) (star c d) ≠ star (star a c) (star b d) := by
  sorry

end Dogma
