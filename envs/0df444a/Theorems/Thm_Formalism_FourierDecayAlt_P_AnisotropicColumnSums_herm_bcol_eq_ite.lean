-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AnisotropicColumnSums_herm_bcol_eq_ite
-- name    : Formalism.FourierDecayAlt.P.AnisotropicColumnSums.herm_bcol_eq_ite
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:34:31.3799+00:00
-- url     : https://prove2.me/theorems/eceb93d5-b04b-4cde-9ee6-7313552f5b55
-- title:
--   Anisotropic Column Sums: herm bcol eq ite
-- statement:
--   The Anisotropic Column Sums construction uses the herm bcol eq ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AnisotropicColumnSums.lean#L99-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AnisotropicColumnSums.lean#L99-L106

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

theorem Formalism.FourierDecayAlt.P.AnisotropicColumnSums.herm_bcol_eq_ite {x : Fin (2 * r + k + 1) → ℂ} {Bs : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hB : IsFrameOf k r [x] Bs) (j : Fin (mdim k r (Fin.last r))) :
    herm (Hpk k r) (bcol k r x Bs j) x = if j.val < k then 0 else herm (Hpk k r) x x := by sorry
