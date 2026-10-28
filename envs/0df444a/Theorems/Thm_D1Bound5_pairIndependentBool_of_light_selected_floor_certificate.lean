-- Prove2me | Theorems.Thm_D1Bound5_pairIndependentBool_of_light_selected_floor_certificate
-- name    : D1Bound5.pairIndependentBool_of_light_selected_floor_certificate
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:14:03.056324+00:00
-- url     : https://prove2.me/theorems/c13fff73-2e21-4be1-a412-2f743ca7bf7b
-- title:
--   Pair Independent Bool of light selected floor certificate
-- statement:
--   Mathematical soundness is reused from the accepted checker only after the unconditional Boolean identity. Positive discriminant is exactly the original soundness premise and is not needed for the computation equality.
-- source:
--   D1Bound5/PairLightArithmeticBridge.lean, lines 168-179, SHA-256 3dadaaf272e22eafa7a7c7429a48fe42dbe591d0dcb73ce8b0f98f6b348b8e51. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Algebra.Order.Ring.Abs
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
import Definitions.Def_D1Bound5_PairLightArithmeticBridge_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5








































theorem _root_.D1Bound5.pairIndependentBool_of_light_selected_floor_certificate {tau nu : ℤ}
    (hd : 0 < QuadInt.discriminant tau nu) (sieve : List (ℕ × ℕ))
    (vertices : List (QuadInt tau nu)) (cached : List (PairResidueVertex tau nu))
    (rows : List (ℕ × List ℕ))
    (hcheck : pairLightSelectedFloorIndependentCertificateBool tau nu sieve
      (vertices.map pairLightCoordinates) (cached.map pairLightCachedCoordinates) rows = true) :
    pairIndependentBool sieve vertices = true := by sorry

end D1Bound5
end
