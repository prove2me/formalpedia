-- Prove2me | Theorems.Thm_D1Bound5_bennett_catalan_rat_recurrence
-- name    : D1Bound5.bennett_catalan_rat_recurrence
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:33:48.502291+00:00
-- url     : https://prove2.me/theorems/af17d037-9cfc-40d6-b266-67bd0cb31452
-- title:
--   Bennett catalan rat recurrence
-- statement:
--   The Catalan recurrence in the form needed for half-binomial coefficients.
-- source:
--   D1Bound5/BennettBinomialIntegrality.lean, lines 18-29, SHA-256 f95293967308ba92e9451def9a6f848adc0cc2ec40690f494052e3d6316f0262. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

section
open Finset

namespace D1Bound5

/-!
The integer denominator bounds used in the Bennett residue construction.
The rational half-binomial identity is proved from the actual Catalan and
central-binomial identities in mathlib, then transported to every
characteristic-zero field. No coefficient-integrality premise is assumed.
-/


theorem _root_.D1Bound5.bennett_catalan_rat_recurrence (n : ℕ) :
    ((n : ℚ) + 2) * (catalan (n + 1) : ℚ) =
      2 * (2 * (n : ℚ) + 1) * (catalan n : ℚ) := by sorry























end D1Bound5
end
