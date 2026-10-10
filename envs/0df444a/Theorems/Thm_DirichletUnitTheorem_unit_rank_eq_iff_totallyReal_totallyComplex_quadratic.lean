-- Prove2me | Theorems.Thm_DirichletUnitTheorem_unit_rank_eq_iff_totallyReal_totallyComplex_quadratic
-- name    : DirichletUnitTheorem.unit_rank_eq_iff_totallyReal_totallyComplex_quadratic
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:33:05.888633+00:00
-- url     : https://prove2.me/theorems/32cfd057-6942-431d-a63f-01f45e5ea6d4
-- title:
--   Equal unit ranks in an extension: $K$ totally real, $L/K$ totally complex quadratic
-- statement:
--   Let $L/K$ be a finite extension of number fields of degree $[L:K]>1$. Then $\mathcal O_L^\times$ and $\mathcal O_K^\times$ have the same rank if and only if $K$ is totally real and $L$ is a totally complex quadratic extension of $K$:
--
--   $$\operatorname{rank}\mathcal O_L^\times=\operatorname{rank}\mathcal O_K^\times \iff K \text{ totally real},\ L \text{ totally complex},\ [L:K]=2.$$
--
--   Example: $K=\mathbb Q$ and $L$ an imaginary quadratic field, both of unit rank $0$.
--
--   **Formalization Note** The ranks are compared as natural numbers (`Module.finrank ℤ`); by Dirichlet's theorem they are finite, so this agrees with the cardinal rank.
-- source:
--   Wikipedia, "Dirichlet's unit theorem" (article supplied by the account owner as a PDF), lead section, paragraph on totally real fields ("If L/K is a finite extension ... with degree greater than 1 and the units groups ... have the same rank then K is totally real and L is a totally complex quadratic extension. The converse holds too.").

import Mathlib
open NumberField

namespace DirichletUnitTheorem

theorem unit_rank_eq_iff_totallyReal_totallyComplex_quadratic (K L : Type*) [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hKL : 1 < Module.finrank K L) :
    Module.finrank ℤ (Additive (𝓞 L)ˣ) = Module.finrank ℤ (Additive (𝓞 K)ˣ) ↔
      IsTotallyReal K ∧ IsTotallyComplex L ∧ Module.finrank K L = 2 := by sorry

end DirichletUnitTheorem
