-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lmulM_cont
-- name    : Formalism.FourierDecayAlt.P.LongWeylElement.lmulM_cont
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:27:19.390791+00:00
-- url     : https://prove2.me/theorems/c5972586-1678-5fc7-919e-ebe4fe058d66
-- title:
--   Long Weyl Element: lmul M cont
-- statement:
--   The Long Weyl Element construction uses the lmul M cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L21-L25

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_lmulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lmulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_lmulM_cont

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

theorem Formalism.FourierDecayAlt.P.LongWeylElement.lmulM_cont {k r : ℕ} (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by sorry
