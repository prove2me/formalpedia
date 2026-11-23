-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lamTil_colOp
-- name    : Formalism.FourierDecayAlt.P.A5x2.lamTil_colOp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:34.746373+00:00
-- url     : https://prove2.me/theorems/eeb725c5-958f-4020-a111-a76b0761ab40
-- title:
--   A5x2: lam Til col Op
-- statement:
--   The A5x2 construction uses the lam Til col Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean#L347-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean#L347-L362

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x2
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
variable {R}
variable (R)

theorem Formalism.FourierDecayAlt.P.A5x2.lamTil_colOp (Z : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z.det) (m : Fin n → R) (c : Fin n)
    (hm : ∀ j, c.val ≤ j → lamTil R Z j m = 0) (j : ℕ) (hj : c.val ≤ j) :
    lamTil R (Z + vecMulVec (coeLin R m) (Pi.single c 1)) j = lamTil R Z j := by sorry
