-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_shf_mem
-- name    : Formalism.FourierDecayAlt.P.A5x9.shf_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:46:28.171835+00:00
-- url     : https://prove2.me/theorems/73ee5aea-5778-4a1d-af52-73ec56a231ce
-- title:
--   A5x9: shf mem
-- statement:
--   The A5x9 construction uses the shf mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L1250-L1260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L1250-L1260

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

theorem Formalism.FourierDecayAlt.P.A5x9.shf_mem (Z₀ p : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z₀.det) (hp : IsPP R k p)
    (m : Fin n → R) (hm : abelian₂ R k Z₀ m = 0) (β : Fin n → K) (hβi : ∀ b, β b ∈ R)
    (hβ : ∀ b : Fin n, b.val ≤ k → β b = 0) (x : Fin n → R) :
    x ∈ latZ R (Z₀ * ((1 + vecMulVec (Z₀⁻¹ *ᵥ coeLin R m) β) * p)) ↔
      ∃ r : R, (r : K) = β ⬝ᵥ (Z₀⁻¹ *ᵥ coeLin R x) ∧ x - r • m ∈ latZ R (Z₀ * p) := by sorry
