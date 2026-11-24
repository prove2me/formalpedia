-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_mul_ltr_pol
-- name    : Formalism.CountingSumsFrames.mul_ltr_pol
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:49.112372+00:00
-- url     : https://prove2.me/theorems/02df026b-f95f-4efb-8ee2-1ea4595d0856
-- title:
--   Counting Sums Frames: mul ltr pol
-- statement:
--   The Counting Sums Frames construction uses the mul ltr pol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L798-L813
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L798-L813

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

theorem Formalism.CountingSumsFrames.mul_ltr_pol (L : Letters N) (j0 : ℕ) {g : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hg : g ∈ Pol p r (Lz L j0))
    {m' : Fin N × Fin r →₀ ℕ} (hm : MultiDeg L m') : g * monomial (ltr (fsj N r j0) m') 1 ∈ Pol p r L := by sorry
