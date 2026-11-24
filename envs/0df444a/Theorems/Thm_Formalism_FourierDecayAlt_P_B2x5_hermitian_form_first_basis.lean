-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_hermitian_form_first_basis
-- name    : Formalism.FourierDecayAlt.P.B2x5.hermitian_form_first_basis
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:58:07.164105+00:00
-- url     : https://prove2.me/theorems/a7a8f18c-22b6-4920-90b4-1ebcdaa8cea4
-- title:
--   B2x5: hermitian form first basis
-- statement:
--   The B2x5 construction uses the hermitian form first basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L133-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L133-L137

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

theorem Formalism.FourierDecayAlt.P.B2x5.hermitian_form_first_basis (k r' : ℕ) (q : Fin (2 * (1 + r') + k + 1)) :
    Hpk k (1 + r') (i0 k r') q = if q = iL k r' then 1 else 0 := by sorry
