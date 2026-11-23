-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_mem_latZ_rank1
-- name    : Formalism.FourierDecayAlt.P.A5x9.mem_latZ_rank1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:46:10.110486+00:00
-- url     : https://prove2.me/theorems/7700e01f-2237-43bb-967b-b906d63f81d2
-- title:
--   A5x9: mem lat Z rank1
-- statement:
--   The A5x9 construction uses the mem lat Z rank1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L612-L644
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L612-L644

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
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)

theorem Formalism.FourierDecayAlt.P.A5x9.mem_latZ_rank1 (Z : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z.det) (m : Fin n → R)
    (β : Fin n → K) (hβ : ∀ b, β b ∈ R) (h0 : β ⬝ᵥ (Z⁻¹ *ᵥ coeLin R m) = 0) (x : Fin n → R) :
    x ∈ latZ R (Z + vecMulVec (coeLin R m) β) ↔
      ∃ r : R, (r : K) = β ⬝ᵥ (Z⁻¹ *ᵥ coeLin R x) ∧ x - r • m ∈ latZ R Z := by sorry
