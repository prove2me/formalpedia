-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_mul_long_weyl_element_apply
-- name    : Formalism.FourierDecayAlt.P.LongWeylElement.mul_long_weyl_element_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:17:20.669529+00:00
-- url     : https://prove2.me/theorems/76d63b33-57f9-432a-9270-80c9dc271563
-- title:
--   Long Weyl Element: mul long weyl element apply
-- statement:
--   The Long Weyl Element construction uses the mul long weyl element apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L147-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L147-L152

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

theorem Formalism.FourierDecayAlt.P.LongWeylElement.mul_long_weyl_element_apply (c : ℂ) (A : Mat k (1 + r')) (i j : Fin (2 * (1 + r') + k + 1)) :
    (A * w0 k r' c) i j = if j.val = 0 then A i (iL k r') * c
      else if j.val = 2 * (1 + r') + k then A i (iZ k r') * (star c)⁻¹ else A i j := by sorry
