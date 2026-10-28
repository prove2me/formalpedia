-- Prove2me | Theorems.Thm_D1Bound5_bennettClearedTaylor_two_poles_scaled_eval
-- name    : D1Bound5.bennettClearedTaylor_two_poles_scaled_eval
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:51:08.494522+00:00
-- url     : https://prove2.me/theorems/2382e823-6194-4d5a-aeae-a80b71263556
-- title:
--   Bennett Cleared Taylor two poles scaled eval
-- statement:
--   Expanding the two actual reciprocal-pole series gives a finite sum with exactly the three Taylor indices used in the manuscript.
-- source:
--   D1Bound5/BennettTwoIntegralEntries.lean, lines 45-62, SHA-256 07d63d84699ae294fc3d395f046972fa36aa179a18de306e5f612beceaaf5f1b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]
















theorem _root_.D1Bound5.bennettClearedTaylor_two_poles_scaled_eval
    (s ν a N d e : F) (k r p q : ℕ) :
    s * (bennettClearedTaylor k r ν a
      (bennettPoleSeries d p * bennettPoleSeries e q)).eval N =
    ∑ ht ∈ Finset.antidiagonal r, ∑ uv ∈ Finset.antidiagonal ht.2,
      s * ((Ring.choose ((k : F) + ν) ht.1 *
        ((Ring.choose (-(p : F)) uv.1 * (d⁻¹) ^ (p + uv.1)) *
          (Ring.choose (-(q : F)) uv.2 * (e⁻¹) ^ (q + uv.2)))) *
            (N + a) ^ (k - ht.1)) := by sorry













end D1Bound5
end
