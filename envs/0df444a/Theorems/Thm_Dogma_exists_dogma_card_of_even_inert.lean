-- Prove2me | Theorems.Thm_Dogma_exists_dogma_card_of_even_inert
-- name    : Dogma.exists_dogma_card_of_even_inert
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T03:32:19.595488+00:00
-- url     : https://prove2.me/theorems/61d8923d-39d6-493e-ac07-47f9a42c688a
-- title:
--   Dogmas exist in every cardinality with even exponents at primes $\equiv \pm 2 \pmod 5$
-- statement:
--   A **dogma** is a right-cancellative magma $(D,\star)$ satisfying $(x\star y)\star y=y\star x$ for all $x,y\in D$. Here right-cancellative means that $x\star z=y\star z$ implies $x=y$.
--
--   Let $n\ge1$ be a positive integer. Suppose that every prime $p$ with $p\equiv 2$ or $p\equiv 3 \pmod 5$ divides $n$ to an **even** power, that is,
--
--   $$
--   v_p(n)\ \text{is even for all primes } p \text{ with } p\equiv \pm 2 \pmod 5 .
--   $$
--
--   Then there exists a dogma of cardinality $n$.
--
--   This gives a large explicit family of cardinalities for the second question of Problem 10 in the CUHK-Shenzhen AI Math Problems (source credited to Ma Li on the problem page), which asks for which $n$ a dogma of cardinality $n$ exists. It contains, for example, $n=1881=3^2\cdot 11\cdot 19$, as well as every perfect square and every product of primes $p\equiv 0,\pm1\pmod 5$. The converse direction is not asserted here.
--
--   **Formalization Note.** The statement is existential over a type $D$ and a binary operation. Cardinality is expressed with `Nat.card`, which is zero for infinite types, so $|D|=n>0$ forces $D$ to be finite. The $p$-adic valuation $v_p(n)$ is `n.factorization p`.
-- source:
--   CUHK-Shenzhen AI Math Problems, Problem 10 (Ma Li), https://rybindmitry.github.io/problems/10.html, question 2: 'For which n does there exist a dogma of cardinality n?' This statement is a sufficient condition (original); the converse is not claimed.

import Mathlib

namespace Dogma

theorem exists_dogma_card_of_even_inert (n : ℕ) (hn : 0 < n)
    (h : ∀ p : ℕ, p.Prime → (p % 5 = 2 ∨ p % 5 = 3) → Even (n.factorization p)) :
    ∃ (D : Type) (star : D → D → D), Nat.card D = n ∧
      (∀ x y z : D, star x z = star y z → x = y) ∧
      ∀ x y : D, star (star x y) y = star y x := by
  sorry

end Dogma
