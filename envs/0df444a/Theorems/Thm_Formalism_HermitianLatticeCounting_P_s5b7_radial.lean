-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5b7_radial
-- name    : Formalism.HermitianLatticeCounting.P.s5b7_radial
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:11.876051+00:00
-- url     : https://prove2.me/theorems/d3d8ee8d-fe04-40a4-91ea-50ac225ca721
-- title:
--   P: s5b7 radial
-- statement:
--   The P construction uses the s5b7 radial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/MeasurePreservingPiCompProd.lean#L620-L667
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/MeasurePreservingPiCompProd.lean#L620-L667

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Module Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate

theorem Formalism.HermitianLatticeCounting.P.s5b7_radial (d r : ℕ) (hr : r ≤ d) (R : ℝ) (hR : 0 < R) :
    ∫⁻ x : EuclideanSpace ℂ (Fin (d + 1)),
      ENNReal.ofReal (if ‖x‖ ≤ R then (‖x‖ ^ (2 * (d - r)))⁻¹ else 0) =
    ENNReal.ofReal (Real.pi ^ (d + 1) / (d.factorial : ℝ) * R ^ (2 * r + 2) / ((r : ℝ) + 1)) := by sorry
