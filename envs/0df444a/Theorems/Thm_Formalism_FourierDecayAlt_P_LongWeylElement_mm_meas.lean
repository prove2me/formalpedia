-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_mm_meas
-- name    : Formalism.FourierDecayAlt.P.LongWeylElement.mm_meas
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:02:48.475453+00:00
-- url     : https://prove2.me/theorems/73fc1dfb-0396-4651-8c30-d35895102066
-- title:
--   Long Weyl Element: mm meas
-- statement:
--   The Long Weyl Element construction uses the mm meas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L732-L736
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L732-L736

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
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
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
variable {k r r' : ℕ}

theorem Formalism.FourierDecayAlt.P.LongWeylElement.mm_meas {α : Type*} [MeasurableSpace α] {A B : α → Mt k r} (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun t => mulM (A t, B t)) := by sorry
