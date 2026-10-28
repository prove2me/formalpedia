-- Prove2me | Theorems.Thm_D1Bound5_bennett_half_choose_scaled_catalan
-- name    : D1Bound5.bennett_half_choose_scaled_catalan
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:32:56.092507+00:00
-- url     : https://prove2.me/theorems/76ca0386-67c6-42ba-bbe6-acc9fe422d3c
-- title:
--   Bennett half choose scaled catalan
-- statement:
--   Exact Catalan formula: multiplying the positive-degree half-binomial coefficient by 4 to its degree gives twice a signed Catalan integer.
-- source:
--   D1Bound5/BennettBinomialIntegrality.lean, lines 40-71, SHA-256 f95293967308ba92e9451def9a6f848adc0cc2ec40690f494052e3d6316f0262. Project: https://github.com/tomislav-math/d1-bound5-lean

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






theorem _root_.D1Bound5.bennett_half_choose_scaled_catalan (n : ℕ) :
    (4 : ℚ) ^ (n + 1) * Ring.choose (1 / 2 : ℚ) (n + 1) =
      (-1 : ℚ) ^ n * 2 * (catalan n : ℚ) := by sorry



















end D1Bound5
end
