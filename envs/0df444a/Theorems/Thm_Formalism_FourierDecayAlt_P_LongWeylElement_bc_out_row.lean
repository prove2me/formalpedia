-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_bc_out_row
-- name    : Formalism.FourierDecayAlt.P.LongWeylElement.bc_out_row
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:27:11.743744+00:00
-- url     : https://prove2.me/theorems/a8ac4155-c23a-5e95-b352-39b94dec80d2
-- title:
--   Long Weyl Element: bc out row
-- statement:
--   The Long Weyl Element construction uses the bc out row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L523-L527
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L523-L527

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
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.LongWeylElement.bc_out_row (c : Fin r → ℂ) (μ ν : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hi : ¬ midW k r i) : bigCell k r c μ i j = bigCell k r c ν i j := by sorry
