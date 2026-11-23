-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_shf_mul
-- name    : Formalism.FourierDecayAlt.P.A5x9.shf_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:46.478334+00:00
-- url     : https://prove2.me/theorems/4fdeb8b0-e1b7-43d7-a7cd-86ffd33cd556
-- title:
--   A5x9: shf mul
-- statement:
--   The A5x9 construction uses the shf mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L1212-L1217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L1212-L1217

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

theorem Formalism.FourierDecayAlt.P.A5x9.shf_mul (Z₀ p : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z₀.det) (m : Fin n → R)
    (β : Fin n → K) :
    Z₀ * ((1 + vecMulVec (Z₀⁻¹ *ᵥ coeLin R m) β) * p) =
      Z₀ * p + vecMulVec (coeLin R m) (β ᵥ* p) := by sorry
