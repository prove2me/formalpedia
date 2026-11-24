-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_levi_position_ne_first
-- name    : Formalism.FourierDecayAlt.P.B2x5.levi_position_ne_first
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:58:35.592042+00:00
-- url     : https://prove2.me/theorems/03b0e998-2db0-4aff-af52-ec3fe3e1761c
-- title:
--   B2x5: levi position ne first
-- statement:
--   The B2x5 construction uses the levi position ne first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L210-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L210-L214

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

theorem Formalism.FourierDecayAlt.P.B2x5.levi_position_ne_first (k r' : ℕ) (j : Fin (2 * r' + k + 1)) : levPos k 1 r' j ≠ i0 k r' := by sorry
