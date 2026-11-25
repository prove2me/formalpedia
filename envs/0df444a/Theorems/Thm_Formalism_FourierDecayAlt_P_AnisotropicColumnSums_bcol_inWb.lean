-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AnisotropicColumnSums_bcol_inWb
-- name    : Formalism.FourierDecayAlt.P.AnisotropicColumnSums.bcol_inWb
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:29:00.788192+00:00
-- url     : https://prove2.me/theorems/b233fbab-10b5-45b8-b988-6f7018488e15
-- title:
--   Anisotropic Column Sums: bcol in Wb
-- statement:
--   The Anisotropic Column Sums construction uses the bcol in Wb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AnisotropicColumnSums.lean#L92-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AnisotropicColumnSums.lean#L92-L97

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.AnisotropicColumnSums
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.AnisotropicColumnSums.bcol_inWb {x : Fin (2 * r + k + 1) → ℂ} {Bs : Fin k → Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x)
    (hB : IsFrameOf k r [x] Bs) (j : Fin (mdim k r (Fin.last r))) : inWb k r (bcol k r x Bs j) := by sorry
