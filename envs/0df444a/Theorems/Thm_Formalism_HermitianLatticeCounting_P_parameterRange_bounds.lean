-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_parameterRange_bounds
-- name    : Formalism.HermitianLatticeCounting.P.parameterRange_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:29:33.28579+00:00
-- url     : https://prove2.me/theorems/47af2f7c-528b-4735-988c-c7b538bc02bc
-- title:
--   P: parameter Range bounds
-- statement:
--   The P construction uses the parameter Range bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExponentInequalityNondegenerateMid.lean#L457-L512
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ExponentInequalityNondegenerateMid.lean#L457-L512

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExponentInequalityNondegenerateMid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P

theorem Formalism.HermitianLatticeCounting.P.parameterRange_bounds (C : ℝ) (hC : 1 ≤ C) (k m f : ℕ) (b g v NT Gam : ℝ)
    (h : Params C (16 * C ^ 32) k m f b g v NT Gam) :
    (4:ℝ) ≤ m ∧ (m:ℝ) ≤ f ∧ (f:ℝ) ≤ k ∧ 0.69 ≤ Real.log b ∧ 1 ≤ Real.log k ∧ 0 ≤ Real.log C ∧
    32 * Real.log C ≤ Real.log k ∧ 8 * (Real.log k + Real.log b) ≤ Real.log g ∧ 0 ≤ Real.log 2 ∧
    Real.log 2 ≤ Real.log b ∧ 16 * C ^ 32 * ((m:ℝ) ^ 5 * f * Real.log b) ≤ k ∧ 0 < g ∧ 0 < b ∧
    0 < v ∧ Real.log v ≤ Real.log b ∧ 0 < NT ∧ Real.log NT ≤ C * m * f * Real.log b ∧ 0 < Gam ∧
    0 ≤ Real.log Gam ∧ Real.log Gam ≤ C * (m:ℝ) ^ 5 * f * Real.log b := by sorry
