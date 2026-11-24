-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_ext_mem_span
-- name    : Formalism.CountingSumsFrames.ext_mem_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:32.07614+00:00
-- url     : https://prove2.me/theorems/71d5aa57-95da-4b88-a127-d7e01ff2ca05
-- title:
--   Counting Sums Frames: ext mem span
-- statement:
--   The Counting Sums Frames construction uses the ext mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1141-L1150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1141-L1150

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

theorem Formalism.CountingSumsFrames.ext_mem_span (j0 : ℕ) (U : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) (hφ : ∀ x, φ x ∈ U)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    ext (fsj N r j0) φ x ∈ Submodule.span ℚ_[p] {x | ∃ g ∈ U,
      ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | j0 ≤ (v.1 : ℕ)}, x = g * q} := by sorry
