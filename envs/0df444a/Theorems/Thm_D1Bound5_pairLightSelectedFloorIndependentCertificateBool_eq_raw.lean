-- Prove2me | Theorems.Thm_D1Bound5_pairLightSelectedFloorIndependentCertificateBool_eq_raw
-- name    : D1Bound5.pairLightSelectedFloorIndependentCertificateBool_eq_raw
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:42:44.218146+00:00
-- url     : https://prove2.me/theorems/93c0c729-00ed-47e0-8de6-c513375c73c8
-- title:
--   Pair Light Selected Floor Independent Certificate Bool eq raw
-- statement:
--   The complete arithmetic-only certificate is exactly the accepted raw certificate for all parameters and all supplied lists. Ordered vertex coverage and every canonical signature are preserved, including malformed data.
-- source:
--   D1Bound5/PairLightArithmeticBridge.lean, lines 155-166, SHA-256 3dadaaf272e22eafa7a7c7429a48fe42dbe591d0dcb73ce8b0f98f6b348b8e51. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_PairCachedResidues_Definitions
import Definitions.Def_D1Bound5_PairLightArithmeticBridge_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_PairRawSelectedFloorWitnesses_Definitions

section
namespace D1Bound5






































theorem _root_.D1Bound5.pairLightSelectedFloorIndependentCertificateBool_eq_raw {tau nu : ℤ}
    (sieve : List (ℕ × ℕ)) (vertices : List (QuadInt tau nu))
    (cached : List (PairResidueVertex tau nu)) (rows : List (ℕ × List ℕ)) :
    pairLightSelectedFloorIndependentCertificateBool tau nu sieve
      (vertices.map pairLightCoordinates) (cached.map pairLightCachedCoordinates) rows =
      pairRawSelectedFloorIndependentCertificateBool sieve vertices cached rows := by sorry



end D1Bound5
end
