-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_shf_vecMul_int
-- name    : Formalism.FourierDecayAlt.P.A5x9.shf_vecMul_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:30.607417+00:00
-- url     : https://prove2.me/theorems/251b0dde-d365-4e14-8c6d-2480b949747b
-- title:
--   A5x9: shf vec Mul int
-- statement:
--   The A5x9 construction uses the shf vec Mul int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L1219-L1226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L1219-L1226

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

theorem Formalism.FourierDecayAlt.P.A5x9.shf_vecMul_int {p : Matrix (Fin n) (Fin n) K} (hp : IsP R k p) (β : Fin n → K)
    (hβi : ∀ b, β b ∈ R) (hβ : ∀ b : Fin n, b.val ≤ k → β b = 0) : ∀ b, (β ᵥ* p) b ∈ R := by sorry
