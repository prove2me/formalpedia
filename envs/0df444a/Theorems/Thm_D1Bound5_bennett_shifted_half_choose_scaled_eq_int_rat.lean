-- Prove2me | Theorems.Thm_D1Bound5_bennett_shifted_half_choose_scaled_eq_int_rat
-- name    : D1Bound5.bennett_shifted_half_choose_scaled_eq_int_rat
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:16:38.951428+00:00
-- url     : https://prove2.me/theorems/e6dee690-3ceb-42f5-be45-06561031d660
-- title:
--   Bennett shifted half choose scaled eq int rat
-- statement:
--   Auxiliary result `bennett_shifted_half_choose_scaled_eq_int_rat` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/BennettBinomialIntegrality.lean, lines 92-107, SHA-256 f95293967308ba92e9451def9a6f848adc0cc2ec40690f494052e3d6316f0262. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Definitions.Def_D1Bound5_BennettBinomialIntegrality_Definitions

section
open Finset

namespace D1Bound5

/-!
The integer denominator bounds used in the Bennett residue construction.
The rational half-binomial identity is proved from the actual Catalan and
central-binomial identities in mathlib, then transported to every
characteristic-zero field. No coefficient-integrality premise is assumed.
-/













theorem _root_.D1Bound5.bennett_shifted_half_choose_scaled_eq_int_rat (k h : ℕ) :
    (4 : ℚ) ^ h * Ring.choose ((k : ℚ) + 1 / 2) h =
      (bennettScaledHalfShiftInt k h : ℚ) := by sorry











end D1Bound5
end
