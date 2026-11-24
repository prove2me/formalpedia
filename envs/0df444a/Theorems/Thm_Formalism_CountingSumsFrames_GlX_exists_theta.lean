-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_GlX_exists_theta
-- name    : Formalism.CountingSumsFrames.GlX.exists_theta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:26.140811+00:00
-- url     : https://prove2.me/theorems/6eb4eda3-5751-47b4-94d2-1a8dc6714803
-- title:
--   Gl X: exists theta
-- statement:
--   The Gl X construction uses the exists theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1180-L1213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1180-L1213

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

theorem Formalism.CountingSumsFrames.GlX.exists_theta {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
    {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {la : Fin r → ℤ} {h h' : V}
    (hh : G.IsHW la h) (hh' : G.IsHW la h') (hhW : h ∈ W) (hh'W : h' ∈ W) (h0 : h ≠ 0) (h0' : h' ≠ 0)
    (π π' : V →ₗ[K] V) (h1 : ∀ x, π x ∈ G.gS {h}) (h2 : ∀ x ∈ G.gS {h}, π x = x)
    (hE : ∀ x ∈ W, ∀ c d, π (G.E c d x) = G.E c d (π x))
    (h1' : ∀ x, π' x ∈ G.gS {h'}) (h2' : ∀ x ∈ G.gS {h'}, π' x = x)
    (hE' : ∀ x ∈ W, ∀ c d, π' (G.E c d x) = G.E c d (π' x)) :
    ∃ θ θ' : V →ₗ[K] V, (∀ x, θ x ∈ G.gS {h'}) ∧ (∀ x ∈ W, ∀ c d, θ (G.E c d x) = G.E c d (θ x)) ∧
      (∀ x, θ' x ∈ G.gS {h}) ∧ (∀ x ∈ W, ∀ c d, θ' (G.E c d x) = G.E c d (θ' x)) ∧
      (∀ x ∈ G.gS {h}, θ' (θ x) = x) := by sorry
