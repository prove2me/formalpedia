-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_weylMatrix_mul_apply
-- name    : Formalism.FourierDecayAlt.P.LongWeylElement.weylMatrix_mul_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:03:03.892618+00:00
-- url     : https://prove2.me/theorems/ce7ecb31-2ee8-4760-8883-a6030a8940e5
-- title:
--   Long Weyl Element: weyl Matrix mul apply
-- statement:
--   The Long Weyl Element construction uses the weyl Matrix mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L132-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L132-L137

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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}

theorem Formalism.FourierDecayAlt.P.LongWeylElement.weylMatrix_mul_apply (c : ℂ) (A : Mat k (1 + r')) (i j : Fin (2 * (1 + r') + k + 1)) :
    (w0 k r' c * A) i j = if i.val = 0 then (star c)⁻¹ * A (iL k r') j
      else if i.val = 2 * (1 + r') + k then c * A (iZ k r') j else A i j := by sorry
