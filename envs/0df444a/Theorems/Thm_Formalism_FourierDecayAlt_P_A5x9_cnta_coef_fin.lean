-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_cnta_coef_fin
-- name    : Formalism.FourierDecayAlt.P.A5x9.cnta_coef_fin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:14:45.76037+00:00
-- url     : https://prove2.me/theorems/f4ccdfad-f941-4c9c-86eb-ab3f70c3782d
-- title:
--   A5x9: cnta coef fin
-- statement:
--   The A5x9 construction uses the cnta coef fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L665-L667
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L665-L667

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

theorem Formalism.FourierDecayAlt.P.A5x9.cnta_coef_fin {D : Matrix (Fin n) (Fin n) K} (hD : IsD R k D) (j b : Fin n) :
    cntaCoef R k hD j b.val = ⟨D j b, hD.2.1 _ _⟩ := by sorry
