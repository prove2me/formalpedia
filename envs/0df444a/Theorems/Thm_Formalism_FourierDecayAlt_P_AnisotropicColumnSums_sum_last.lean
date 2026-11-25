-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AnisotropicColumnSums_sum_last
-- name    : Formalism.FourierDecayAlt.P.AnisotropicColumnSums.sum_last
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:30:03.154476+00:00
-- url     : https://prove2.me/theorems/a12e1b8d-f568-4ff5-8ca6-170602350c4a
-- title:
--   Anisotropic Column Sums: sum last
-- statement:
--   The Anisotropic Column Sums construction uses the sum last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AnisotropicColumnSums.lean#L37-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AnisotropicColumnSums.lean#L37-L80

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

theorem Formalism.FourierDecayAlt.P.AnisotropicColumnSums.sum_last {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (w : Fin (2 * r + k + 1) → ℂ) :
    ∑ d, herm (Hpk k r) (bvec (posL k r (Fin.last r) d)) w * v (posL k r (Fin.last r) d) = herm (Hpk k r) v w := by sorry
