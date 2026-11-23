-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_grp_mem_PPsub
-- name    : Formalism.FourierDecayAlt.P.A5x9.grp_mem_PPsub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:46:15.922117+00:00
-- url     : https://prove2.me/theorems/25a863b0-c4ae-46b0-ba5a-0dfc083333ec
-- title:
--   A5x9: grp mem PPsub
-- statement:
--   The A5x9 construction uses the grp mem PPsub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L1433-L1434
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L1433-L1434

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
noncomputable section
variable {K : Type} [CommRing K] (R : Subring K) (k : ℕ)

theorem Formalism.FourierDecayAlt.P.A5x9.grp_mem_PPsub {N : ℕ} (u : upUniG K N) :
    u ∈ PPsub R k N ↔ IsPP R k ((u : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by sorry
