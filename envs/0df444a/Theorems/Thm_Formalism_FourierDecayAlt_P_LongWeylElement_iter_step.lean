-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_iter_step
-- name    : Formalism.FourierDecayAlt.P.LongWeylElement.iter_step
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:16:56.086299+00:00
-- url     : https://prove2.me/theorems/fac972a4-c61e-4799-be7d-5a6b24a32c61
-- title:
--   Long Weyl Element: iter step
-- statement:
--   The Long Weyl Element construction uses the iter step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L983-L1097
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L983-L1097

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

theorem Formalism.FourierDecayAlt.P.LongWeylElement.iter_step (hO : OneStepInt) (HU : HaarUnique) (hL : LevHaar) (hCN : ClosedN) (hCb : ClosedWb)
    (hG : HaarGExists) (hNe : HaarNExists) (hWb : HaarWbExists) (hNR : NRecHaar) (hC : HeisConjLevMeas)
    (k r' : ℕ) (ih : IterAt k r') : IterAt k (1 + r') := by sorry
