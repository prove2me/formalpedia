-- Prove2me | Theorems.Thm_D1Bound5_pairCachedIndependentBool_sound
-- name    : D1Bound5.pairCachedIndependentBool_sound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:00:26.769916+00:00
-- url     : https://prove2.me/theorems/759c9890-f2d7-4705-8d8c-99748352b278
-- title:
--   Pair Cached Independent Bool sound
-- statement:
--   Auxiliary result `pairCachedIndependentBool_sound` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/PairCachedResidues.lean, lines 94-123, SHA-256 8d30539028d401e948637a33f705cb33707d8ad4e1fe939eafd5ed7c690a9100. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairBipartiteCheck_Definitions
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions

section
namespace D1Bound5





















theorem _root_.D1Bound5.pairCachedIndependentBool_sound {tau nu : ℤ} (sieve : List (ℕ × ℕ))
    (cached : List (PairResidueVertex tau nu))
    (hvalid : ∀ x ∈ cached, x.signature = pairCoordinateSignature sieve x.vertex)
    (hcheck : pairCachedIndependentBool sieve cached = true) :
    pairIndependentBool sieve (cached.map PairResidueVertex.vertex) = true := by sorry





end D1Bound5
end
