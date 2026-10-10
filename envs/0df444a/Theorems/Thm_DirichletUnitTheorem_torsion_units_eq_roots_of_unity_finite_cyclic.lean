-- Prove2me | Theorems.Thm_DirichletUnitTheorem_torsion_units_eq_roots_of_unity_finite_cyclic
-- name    : DirichletUnitTheorem.torsion_units_eq_roots_of_unity_finite_cyclic
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:32:18.525031+00:00
-- url     : https://prove2.me/theorems/cc8afec5-72a1-425d-9105-1b9f4dbcc60a
-- title:
--   Torsion units are the roots of unity and form a finite cyclic group
-- statement:
--   Let $K$ be a number field. The torsion subgroup of $\mathcal O_K^\times$ is the set of all roots of unity of $K$, and it is a finite cyclic group. Precisely:
--
--   1. an element $x\in K$ is a unit of $\mathcal O_K$ of finite order if and only if $x^n=1$ for some integer $n\ge 1$;
--   2. the torsion subgroup of $\mathcal O_K^\times$ is finite;
--   3. the torsion subgroup of $\mathcal O_K^\times$ is cyclic.
-- source:
--   Wikipedia, "Dirichlet's unit theorem" (article supplied by the account owner as a PDF), lead section, paragraph on torsion ("The torsion in the group of units is the set of all roots of unity of K, which form a finite cyclic group").

import Mathlib
open NumberField

namespace DirichletUnitTheorem

theorem torsion_units_eq_roots_of_unity_finite_cyclic (K : Type*) [Field K] [NumberField K] :
    (∀ x : K, (∃ u : (𝓞 K)ˣ, IsOfFinOrder u ∧ ((u : 𝓞 K) : K) = x) ↔
        ∃ n : ℕ, 0 < n ∧ x ^ n = 1) ∧
      Finite (CommGroup.torsion (𝓞 K)ˣ) ∧ IsCyclic (CommGroup.torsion (𝓞 K)ˣ) := by sorry

end DirichletUnitTheorem
