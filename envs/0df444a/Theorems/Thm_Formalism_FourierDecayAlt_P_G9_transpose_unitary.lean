-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G9_transpose_unitary
-- name    : Formalism.FourierDecayAlt.P.G9.transpose_unitary
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:30.66772+00:00
-- url     : https://prove2.me/theorems/c6616c2a-c444-4f84-afe8-ff1be25b2826
-- title:
--   G9: transpose unitary
-- statement:
--   The G9 construction uses the transpose unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussianHessianIntegral.lean#L355-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussianHessianIntegral.lean#L355-L362

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G9

theorem Formalism.FourierDecayAlt.P.G9.transpose_unitary {d : ℕ} {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) : Wᵀ ∈ Matrix.unitaryGroup (Fin d) ℂ := by sorry
