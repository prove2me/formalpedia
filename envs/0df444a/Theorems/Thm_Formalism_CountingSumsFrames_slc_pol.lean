-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_slc_pol
-- name    : Formalism.CountingSumsFrames.slc_pol
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:25.547798+00:00
-- url     : https://prove2.me/theorems/1220bd47-1973-44c6-829d-8bfbc8a2dd68
-- title:
--   Counting Sums Frames: slc pol
-- statement:
--   The Counting Sums Frames construction uses the slc pol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L768-L785
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L768-L785

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

theorem Formalism.CountingSumsFrames.slc_pol (L : Letters N) (j0 : ℕ) (m : Fin N × Fin r →₀ ℕ) {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ Pol p r L) : slc (fsj N r j0) m x ∈ Pol p r (Lz L j0) := by sorry
