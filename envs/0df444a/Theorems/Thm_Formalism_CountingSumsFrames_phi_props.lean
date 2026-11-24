-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_phi_props
-- name    : Formalism.CountingSumsFrames.phi_props
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:45:39.198872+00:00
-- url     : https://prove2.me/theorems/f8effea8-7682-48b7-ba82-ef8ed912541c
-- title:
--   Counting Sums Frames: phi props
-- statement:
--   The Counting Sums Frames construction uses the phi props property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1001-L1018
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1001-L1018

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.CountingSumsFrames.phi_props (L : Letters N) (j0 : ℕ)
    (π : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hπP : ∀ x ∈ Pol p r (Lz L j0), π x ∈ Pol p r (Lz L j0))
    (hπE : ∀ x ∈ Pol p r (Lz L j0), ∀ c d, π (glAct p L j0 c d x) = glAct p L j0 c d (π x))
    (hπc : ∀ x ∈ Pol p r (Lz L j0), ∀ ν, π ((GA p L j0).comp ν x) = (GA p L j0).comp ν (π x)) :
    (∀ c d x, (π ∘ₗ psi p L j0) (glAct p L j0 c d x) = glAct p L j0 c d ((π ∘ₗ psi p L j0) x)) ∧
    (∀ ν x, x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν →
      (π ∘ₗ psi p L j0) x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν) ∧
    (∀ x, (π ∘ₗ psi p L j0) x ∈ Pol p r (Lz L j0)) := by sorry
