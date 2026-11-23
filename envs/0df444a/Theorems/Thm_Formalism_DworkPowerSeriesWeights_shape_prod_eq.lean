-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_shape_prod_eq
-- name    : Formalism.DworkPowerSeriesWeights.shape_prod_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:04:03.270797+00:00
-- url     : https://prove2.me/theorems/ce21e174-7801-47b8-a936-77116c95b2d6
-- title:
--   Dwork Power Series Weights: shape prod eq
-- statement:
--   The Dwork Power Series Weights construction uses the shape prod eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/MinorProductSupportTop.lean#L17-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/MinorProductSupportTop.lean#L17-L35

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementH
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MinorProductSupportTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial
variable {σ : Type}

theorem Formalism.DworkPowerSeriesWeights.shape_prod_eq {R : Type u} [CommRing R] {ι : Type*} (g : (σ →₀ ℕ) → ℕ) (hg0 : g 0 = 0)
    (hgadd : ∀ a b, g (a + b) = g a + g b) (f : ι → MvPolynomial σ R) (a : ι → ℕ) (s : Finset ι)
    (h : ∀ c ∈ s, ∀ mono ∈ (f c).support, g mono = a c) :
    ∀ mono ∈ (∏ c ∈ s, f c).support, g mono = ∑ c ∈ s, a c := by sorry
