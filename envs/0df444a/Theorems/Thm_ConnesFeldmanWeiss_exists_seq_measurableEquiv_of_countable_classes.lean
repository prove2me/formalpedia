-- Prove2me | Theorems.Thm_ConnesFeldmanWeiss_exists_seq_measurableEquiv_of_countable_classes
-- name    : ConnesFeldmanWeiss.exists_seq_measurableEquiv_of_countable_classes
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T14:44:40.929828+00:00
-- url     : https://prove2.me/theorems/c3028492-8865-4252-af4d-3b8b52e27d74
-- title:
--   Proof of Lemma 3 (external, Feldman–Moore) — a countable Borel equivalence relation is a countable union of graphs of Borel automorphisms
-- statement:
--   Let $X$ be a standard Borel space and $R \subseteq X \times X$ a Borel equivalence relation whose classes are countable. Then there are Borel automorphisms $\phi_0, \phi_1, \dots$ of $X$ (bijections, measurable with measurable inverse) such that $(x, y) \in R$ exactly when $y = \phi_n(x)$ for some $n$: $R$ is the union of the graphs of the $\phi_n$.
--
--   No measure is involved. Feldman and Moore's Theorem 1 gives more, a countable group of Borel automorphisms whose orbits are the classes; the statement is the form the proof of Lemma 3 uses.
-- source:
--   Feldman, J., Moore, C. C., Ergodic equivalence relations, cohomology, and von Neumann algebras. I, Trans. Amer. Math. Soc. 234 (1977) 289–324, https://doi.org/10.1090/S0002-9947-1977-0578656-4, p. 435, proof of Lemma 3

import Mathlib

namespace ConnesFeldmanWeiss

theorem exists_seq_measurableEquiv_of_countable_classes {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] (R : Set (X × X)) (hR : MeasurableSet R)
    (hequiv : Equivalence fun x y => (x, y) ∈ R) (hcount : ∀ x, {y | (x, y) ∈ R}.Countable) :
    ∃ φ : ℕ → X ≃ᵐ X, ∀ x y, (x, y) ∈ R ↔ ∃ n, φ n x = y := by
  sorry

end ConnesFeldmanWeiss
