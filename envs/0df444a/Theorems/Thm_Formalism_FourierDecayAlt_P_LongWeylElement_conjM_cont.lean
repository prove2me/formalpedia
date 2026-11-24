-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_conjM_cont
-- name    : Formalism.FourierDecayAlt.P.LongWeylElement.conjM_cont
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:16:25.513051+00:00
-- url     : https://prove2.me/theorems/f12edcea-e607-470e-981b-a8bb7e9adb8d
-- title:
--   Long Weyl Element: conj M cont
-- statement:
--   The Long Weyl Element construction uses the conj M cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L15-L19

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_conjM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_conjM_cont

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

theorem Formalism.FourierDecayAlt.P.LongWeylElement.conjM_cont {k r : ℕ} (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) := by sorry
