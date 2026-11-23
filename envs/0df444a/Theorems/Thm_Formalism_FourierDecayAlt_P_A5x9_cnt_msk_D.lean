-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_cnt_msk_D
-- name    : Formalism.FourierDecayAlt.P.A5x9.cnt_msk_D
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:43.758076+00:00
-- url     : https://prove2.me/theorems/76f8aaf3-4b93-465b-a39f-6d111c9cabcd
-- title:
--   A5x9: cnt msk D
-- statement:
--   The A5x9 construction uses the cnt msk D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L844-L846
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L844-L846

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
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)

theorem Formalism.FourierDecayAlt.P.A5x9.cnt_msk_D {D : Matrix (Fin n) (Fin n) K} (hD : IsD R k D) (Z : Matrix (Fin n) (Fin n) K)
    (x : Fin n → R) : msk k (D *ᵥ abelian₂ R k Z x) = D *ᵥ abelian₂ R k Z x := by sorry
