-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G9_unitary_mp
-- name    : Formalism.FourierDecayAlt.P.G9.unitary_mp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:34.405793+00:00
-- url     : https://prove2.me/theorems/65f9da2c-72b6-4a51-9fa8-433c02edee23
-- title:
--   G9: unitary mp
-- statement:
--   The G9 construction uses the unitary mp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussianHessianIntegral.lean#L321-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussianHessianIntegral.lean#L321-L339

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

theorem Formalism.FourierDecayAlt.P.G9.unitary_mp (d : ℕ) (β : ℂ) (hβ : β ≠ 0) (W : Matrix (Fin d) (Fin d) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    MeasurePreserving (fun x : Fin d → ℂ => W *ᵥ x) (muPi β (Fin d)) (muPi β (Fin d)) := by sorry
