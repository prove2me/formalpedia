-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_shf_dot
-- name    : Formalism.FourierDecayAlt.P.A5x9.shf_dot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:46:18.330611+00:00
-- url     : https://prove2.me/theorems/a83a7f24-7679-45f9-9c89-7a263719f5c5
-- title:
--   A5x9: shf dot
-- statement:
--   The A5x9 construction uses the shf dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L1228-L1232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L1228-L1232

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

theorem Formalism.FourierDecayAlt.P.A5x9.shf_dot (Z₀ p : Matrix (Fin n) (Fin n) K) (hp : IsUpUni p) (β v : Fin n → K) :
    (β ᵥ* p) ⬝ᵥ ((Z₀ * p)⁻¹ *ᵥ v) = β ⬝ᵥ (Z₀⁻¹ *ᵥ v) := by sorry
