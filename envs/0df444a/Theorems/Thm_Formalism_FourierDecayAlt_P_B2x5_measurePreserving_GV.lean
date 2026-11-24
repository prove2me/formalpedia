-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_measurePreserving_GV
-- name    : Formalism.FourierDecayAlt.P.B2x5.measurePreserving_GV
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:59:26.093847+00:00
-- url     : https://prove2.me/theorems/1334e438-5b04-4383-8309-9425225c3fdf
-- title:
--   B2x5: measure Preserving GV
-- statement:
--   The B2x5 construction uses the measure Preserving GV property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L710-L723
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L710-L723

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

theorem Formalism.FourierDecayAlt.P.B2x5.measurePreserving_GV {k r : ℕ} {g : Mat k r} (hg : g ∈ GV k r) :
    MeasurePreserving (fun y : Fin (2 * r + k + 1) → ℂ => g *ᵥ y) volume volume := by sorry
