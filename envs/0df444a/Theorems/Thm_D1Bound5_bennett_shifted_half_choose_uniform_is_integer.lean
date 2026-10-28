-- Prove2me | Theorems.Thm_D1Bound5_bennett_shifted_half_choose_uniform_is_integer
-- name    : D1Bound5.bennett_shifted_half_choose_uniform_is_integer
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:15.739673+00:00
-- url     : https://prove2.me/theorems/a9d7b58d-5902-4688-8e48-9930f1ed8dca
-- title:
--   Bennett shifted half choose uniform is integer
-- statement:
--   A larger uniform power of four clears every coefficient below its degree bound. This is the form used for a whole order-k residue row.
-- source:
--   D1Bound5/BennettBinomialIntegrality.lean, lines 126-141, SHA-256 f95293967308ba92e9451def9a6f848adc0cc2ec40690f494052e3d6316f0262. Project: https://github.com/tomislav-math/d1-bound5-lean

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




















theorem _root_.D1Bound5.bennett_shifted_half_choose_uniform_is_integer
    {F : Type*} [Field F] [CharZero F] (k h K : ℕ) (hh : h ≤ K) :
    ∃ z : ℤ, (4 : F) ^ K * Ring.choose ((k : F) + 1 / 2) h = (z : F) := by sorry





end D1Bound5
end
