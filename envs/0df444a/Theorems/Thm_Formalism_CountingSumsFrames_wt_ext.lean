-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_wt_ext
-- name    : Formalism.CountingSumsFrames.wt_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:45:49.239136+00:00
-- url     : https://prove2.me/theorems/68ae9ca0-4501-4ecf-afdc-b704a3a65865
-- title:
--   Counting Sums Frames: wt ext
-- statement:
--   The Counting Sums Frames construction uses the wt ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1524-L1533
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1524-L1533

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
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}

theorem Formalism.CountingSumsFrames.wt_ext (LL : Letters K) (n : ℕ) (ρ c : Fin r) (m' : Fin K × Fin r →₀ ℕ) :
    wt (LL.snoc n) (K + 1) c (FB.ext n ρ m') = wt LL K c m' - (if c = ρ then (n : ℤ) else 0) := by sorry
