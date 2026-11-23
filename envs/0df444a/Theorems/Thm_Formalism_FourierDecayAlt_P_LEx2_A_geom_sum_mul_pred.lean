-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_A_geom_sum_mul_pred
-- name    : Formalism.FourierDecayAlt.P.LEx2.A.geom_sum_mul_pred
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:19:28.588905+00:00
-- url     : https://prove2.me/theorems/7baa2b4e-0247-4fdb-ac0c-6bd1b06c3275
-- title:
--   A: geom sum mul pred
-- statement:
--   The A construction uses the geom sum mul pred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ShiftBound.lean#L159-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ShiftBound.lean#L159-L166

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2 Formalism.FourierDecayAlt.P.LEx2.A
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section

theorem Formalism.FourierDecayAlt.P.LEx2.A.geom_sum_mul_pred (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1/2) (R : ℕ) : ∑ p ∈ Icc 1 R, x ^ p ≤ 2 * x - 2 * x ^ (R + 1) := by sorry
