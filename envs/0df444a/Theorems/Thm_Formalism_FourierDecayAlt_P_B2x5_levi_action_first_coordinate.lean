-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_levi_action_first_coordinate
-- name    : Formalism.FourierDecayAlt.P.B2x5.levi_action_first_coordinate
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:43:20.599793+00:00
-- url     : https://prove2.me/theorems/65bf308f-5278-4432-9be4-49d71145f95e
-- title:
--   B2x5: levi action first coordinate
-- statement:
--   The B2x5 construction uses the levi action first coordinate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L531-L533
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L531-L533

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

theorem Formalism.FourierDecayAlt.P.B2x5.levi_action_first_coordinate (k r' : ℕ) (g : Mat k r') (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    (ιLev k 1 r' g *ᵥ u) (i0 k r') = u (i0 k r') := by sorry
