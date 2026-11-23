-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_shape_prod_le
-- name    : Formalism.DworkPowerSeriesWeights.shape_prod_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:04:20.654425+00:00
-- url     : https://prove2.me/theorems/5d3a5833-16ae-4a3f-95eb-d82555a46b98
-- title:
--   Dwork Power Series Weights: shape prod le
-- statement:
--   The Dwork Power Series Weights construction uses the shape prod le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/MinorProductSupportTop.lean#L37-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/MinorProductSupportTop.lean#L37-L56

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

theorem Formalism.DworkPowerSeriesWeights.shape_prod_le {R : Type u} [CommRing R] {ι : Type*} (g : (σ →₀ ℕ) → ℕ) (hg0 : g 0 = 0)
    (hgadd : ∀ a b, g (a + b) = g a + g b) (f : ι → MvPolynomial σ R) (a : ι → ℕ) (s : Finset ι)
    (h : ∀ c ∈ s, ∀ mono ∈ (f c).support, g mono ≤ a c) :
    ∀ mono ∈ (∏ c ∈ s, f c).support, g mono ≤ ∑ c ∈ s, a c := by sorry
