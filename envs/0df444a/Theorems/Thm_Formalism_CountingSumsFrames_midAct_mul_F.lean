-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_midAct_mul_F
-- name    : Formalism.CountingSumsFrames.midAct_mul_F
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:40.650538+00:00
-- url     : https://prove2.me/theorems/997c42f1-fe9a-4a42-8111-0074942f3739
-- title:
--   Counting Sums Frames: mid Act mul F
-- statement:
--   The Counting Sums Frames construction uses the mid Act mul F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L824-L830
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L824-L830

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

theorem Formalism.CountingSumsFrames.midAct_mul_F (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (c d : Fin r) {g q : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hg : IsF (fsj N r j0) g) : midAct p L j0 J c d (g * q) = g * midAct p L j0 J c d q := by sorry
