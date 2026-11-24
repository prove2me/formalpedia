-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_shear
-- name    : Formalism.FourierDecayAlt.P.B2x5.shear
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:42:57.987295+00:00
-- url     : https://prove2.me/theorems/db619ea5-3d1a-4582-b372-96e32597ea28
-- title:
--   B2x5: shear
-- statement:
--   The B2x5 construction uses the shear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L644-L648
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L644-L648

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem Formalism.FourierDecayAlt.P.B2x5.shear (k r' : ℕ) {f : (Fin (2 * r' + k + 1) → ℂ) → (Fin (2 * r' + k + 1) → ℂ)}
    (hf : MeasurePreserving f volume volume) {c : (Fin (2 * r' + k + 1) → ℂ) → ℝ} (hc : Measurable c) :
    MeasurePreserving (fun p : HPar k r' => (f p.1, p.2 + c p.1)) volume volume := by sorry
