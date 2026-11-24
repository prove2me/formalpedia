-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_e0_eq
-- name    : Formalism.FourierDecayAlt.P.B2x5.e0_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:41:53.6028+00:00
-- url     : https://prove2.me/theorems/dcd5c403-b2b1-43ed-83e3-defc988587b2
-- title:
--   B2x5: e0 eq
-- statement:
--   The B2x5 construction uses the e0 eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L223-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L223-L223

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

theorem Formalism.FourierDecayAlt.P.B2x5.e0_eq (k r' : ℕ) : e0 k r' = Pi.single (i0 k r') 1 := by sorry
