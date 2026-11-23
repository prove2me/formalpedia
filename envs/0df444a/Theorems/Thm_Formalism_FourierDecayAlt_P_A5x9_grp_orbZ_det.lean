-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_grp_orbZ_det
-- name    : Formalism.FourierDecayAlt.P.A5x9.grp_orbZ_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:59.331913+00:00
-- url     : https://prove2.me/theorems/6d83e62f-38fb-4c14-8e7f-30f5af38dac5
-- title:
--   A5x9: grp orb Z det
-- statement:
--   The A5x9 construction uses the grp orb Z det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L1445-L1450
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L1445-L1450

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

theorem Formalism.FourierDecayAlt.P.A5x9.grp_orbZ_det (w : Point K) (p : lowW K w.1 w.2 × upUniG K w.1.sum) :
    IsUnit (orbZ w p).det := by sorry
