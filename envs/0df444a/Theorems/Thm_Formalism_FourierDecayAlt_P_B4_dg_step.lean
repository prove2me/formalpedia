-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dg_step
-- name    : Formalism.FourierDecayAlt.P.B4.dg_step
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:30:27.493346+00:00
-- url     : https://prove2.me/theorems/a8acbef0-1c0c-4ba6-b1f4-913339b6ea8a
-- title:
--   B4: dg step
-- statement:
--   The B4 construction uses the dg step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L87-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L87-L93

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.B4.dg_step (k r : ℕ) (t : ℝ) (ht : t ≠ 0) (a : Fin r) (h : a.val + 1 < r) :
    dg k r t (eI k r a) * dg k r t⁻¹ (eI k r ⟨a.val + 1, h⟩) = (t : ℂ) := by sorry
