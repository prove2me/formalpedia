-- Prove2me | Theorems.Thm_FamousTheorems_pythagorean_triple_classification
-- name    : FamousTheorems.pythagorean_triple_classification
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:30:24.086602+00:00
-- url     : https://prove2.me/theorems/94ea710a-6f77-41ed-ba69-bdbdc6d9883e
-- title:
--   Formula for Pythagorean triples (Euclid's parametrization)
-- statement:
--   **Euclid's parametrization of the Pythagorean triples.**
--
--   An integer triple $(x,y,z)$ satisfies $x^2+y^2=z^2$ if and only if there are integers $k,m,n$ with
--   $$\{x,y\} = \{k(m^2-n^2),\; 2kmn\}, \qquad z = \pm k(m^2+n^2).$$
--
--   So every right triangle with integer sides is a scaled copy of one built from a pair $(m,n)$, and the
--   classification is exhaustive: the $\leftrightarrow$ says nothing else occurs. The unordered pair
--   $\{x,y\}$ appears as a disjunction because the two legs play asymmetric roles in the formula — one is
--   a difference of squares, the other is twice a product — while the triple itself does not care which is
--   which. The sign on $z$ is present because the statement is over $\mathbb{Z}$, not $\mathbb{N}$.
--
--   The parametrization is in Book X of Euclid's *Elements*; Diophantus used it, and the Babylonian tablet
--   Plimpton 322 (c. 1800 BC) appears to tabulate triples generated this way, over a thousand years earlier.
--   It is the first nontrivial Diophantine equation to be completely solved, and the starting point for
--   Fermat's descent — the $n=4$ case of Fermat's Last Theorem is proved by feeding this classification
--   back into itself.
--
--   **Formalization note.** `PythagoreanTriple x y z` unfolds to `x * x + y * y = z * z`. The result is
--   Mathlib's `PythagoreanTriple.classification`.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem pythagorean_triple_classification : ∀ {x y z : ℤ}, PythagoreanTriple x y z ↔
    ∃ k m n, (x = k * (m ^ 2 - n ^ 2) ∧ y = k * (2 * m * n) ∨
        x = k * (2 * m * n) ∧ y = k * (m ^ 2 - n ^ 2)) ∧
      (z = k * (m ^ 2 + n ^ 2) ∨ z = -k * (m ^ 2 + n ^ 2)) := by sorry

end FamousTheorems
