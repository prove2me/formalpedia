-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_grp_sUp_conj
-- name    : Formalism.FourierDecayAlt.P.A5x9.grp_sUp_conj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:46:04.439557+00:00
-- url     : https://prove2.me/theorems/43c86559-689c-49be-8dee-d61ff597a593
-- title:
--   A5x9: grp s Up conj
-- statement:
--   The A5x9 construction uses the grp s Up conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L1487-L1493
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L1487-L1493

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

theorem Formalism.FourierDecayAlt.P.A5x9.grp_sUp_conj {N : ℕ} (a b : upUniG K N) :
    sUp (((a * b * a⁻¹ : upUniG K N) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
      sUp ((b : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by sorry
