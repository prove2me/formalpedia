-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lamTil_eLast
-- name    : Formalism.FourierDecayAlt.P.A5x2.lamTil_eLast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:02:06.584571+00:00
-- url     : https://prove2.me/theorems/c973fbba-038d-4de6-aeb0-966b6a42483b
-- title:
--   A5x2: lam Til e Last
-- statement:
--   The A5x2 construction uses the lam Til e Last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean#L366-L376
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean#L366-L376

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

theorem Formalism.FourierDecayAlt.P.A5x2.lamTil_eLast {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
    (Z : Matrix (Fin n) (Fin n) K) (a b : Fin n) (hb : b.val + 1 = n) :
    lamTil R Z a.val (eLast R) = Z⁻¹ a b := by sorry
