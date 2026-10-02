-- Prove2me | Theorems.Thm_DiazModulus_no_algebraic_generalized_line_unconditional
-- name    : DiazModulus.no_algebraic_generalized_line_unconditional
-- status  : Open
-- author  : @carlok
-- created : 2026-10-02T11:28:55.317293+00:00
-- url     : https://prove2.me/theorems/13fcac6a-e039-453b-a9d8-9991dee320aa
-- title:
--   A logarithm off the axes lies on no algebraic generalized line, unconditionally
-- statement:
--   A logarithm $\lambda$ of an algebraic number lying off both coordinate axes lies on no algebraic generalized line: there are no $B \in \overline{\mathbb{Q}}^{\times}$ and $C \in \overline{\mathbb{Q}}$ with $$B\lambda + \overline{B}\,\overline{\lambda} + C = 0 .$$
--
--   This is `DiazModulus.no_algebraic_generalized_line` with its hypothesis, Baker's theorem for two logarithms, discharged by `DiazModulus.baker_two_logs`, which this mission proves following Chapter 4 of Waldschmidt's *Diophantine Approximation on Linear Algebraic Groups*.
--
--   **Proof.** `DiazModulus.no_algebraic_generalized_line DiazModulus.baker_two_logs`.
--
--   **Novelty.** Nothing beyond the parent node; its page gives the argument and the attribution.
-- source:
--   The statement and argument of `DiazModulus.no_algebraic_generalized_line` (Theorem 6.1 of the companion note, version 1.9; the first step of Théorème 3 in G. Diaz, J. Théor. Nombres Bordeaux 16 (2004)), with Baker's theorem (A. Baker, Linear forms in the logarithms of algebraic numbers I, Mathematika 13 (1966), 204–216) proved in this mission as `DiazModulus.baker_two_logs`. Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem no_algebraic_generalized_line_unconditional :
    ∀ l : ℂ, IsAlgebraic ℚ (Complex.exp l) → l.re ≠ 0 → l.im ≠ 0 →
      ∀ B C : ℂ, IsAlgebraic ℚ B → B ≠ 0 → IsAlgebraic ℚ C →
        B * l + (starRingEnd ℂ) B * (starRingEnd ℂ) l + C ≠ 0 := by
  sorry

end DiazModulus
