-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_inv_pow_bounds
-- name    : Formalism.FourierDecayAlt.P.Sz2.inv_pow_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:59.475062+00:00
-- url     : https://prove2.me/theorems/3a6aebf3-8dfd-4147-b0b2-3d2fdaef6625
-- title:
--   Sz2: inv pow bounds
-- statement:
--   The Sz2 construction uses the inv pow bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CorollaryAOfPropositionA.lean#L98-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CorollaryAOfPropositionA.lean#L98-L106

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz2
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz2.inv_pow_bounds (q j : ℕ) (hq : 2 ≤ q) (hj : 1 ≤ j) :
    0 ≤ ((q : ℝ) ^ j)⁻¹ ∧ ((q : ℝ) ^ j)⁻¹ ≤ 1 / 2 ^ j ∧ (1 : ℝ) / 2 ^ j ≤ 1 / 2 := by sorry
