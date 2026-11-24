-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_monomial_ltr_supported
-- name    : Formalism.CountingSumsFrames.monomial_ltr_supported
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:38.66392+00:00
-- url     : https://prove2.me/theorems/03c220de-450f-48c9-87ba-3c6997e66aae
-- title:
--   Counting Sums Frames: monomial ltr supported
-- statement:
--   The Counting Sums Frames construction uses the monomial ltr supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1133-L1139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1133-L1139

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

theorem Formalism.CountingSumsFrames.monomial_ltr_supported (j0 : ℕ) (m : Fin N × Fin r →₀ ℕ) :
    (monomial (ltr (fsj N r j0) m) (1 : ℚ_[p])) ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | j0 ≤ (v.1 : ℕ)} := by sorry
