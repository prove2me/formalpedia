-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_ext_rep
-- name    : Formalism.CountingSumsFrames.ext_rep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:36.878973+00:00
-- url     : https://prove2.me/theorems/4a6e6106-01b3-453e-a32f-1d84787cb067
-- title:
--   Counting Sums Frames: ext rep
-- statement:
--   The Counting Sums Frames construction uses the ext rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1160-L1172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1160-L1172

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

theorem Formalism.CountingSumsFrames.ext_rep (L : Letters N) (j0 : ℕ) (U : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hU : U ≤ Pol p r (Lz L j0)) {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ Submodule.span ℚ_[p] {x | ∃ g ∈ U,
      ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | j0 ≤ (v.1 : ℕ)}, x = g * q}) :
    ∃ s : Finset (Fin N × Fin r →₀ ℕ), ∃ a : (Fin N × Fin r →₀ ℕ) → MvPolynomial (Fin N × Fin r) ℚ_[p],
      (∀ b, a b ∈ U) ∧ x = ∑ b ∈ s, a b * monomial b 1 ∧
      ∀ a' : (Fin N × Fin r →₀ ℕ) → MvPolynomial (Fin N × Fin r) ℚ_[p], (∀ b, a' b ∈ Pol p r (Lz L j0)) →
        ∀ φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p],
        ext (fsj N r j0) φ (∑ b ∈ s, a' b * monomial b 1) = ∑ b ∈ s, φ (a' b) * monomial b 1 := by sorry
