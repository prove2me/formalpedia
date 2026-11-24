-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_slc_glAct
-- name    : Formalism.CountingSumsFrames.slc_glAct
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:02.509832+00:00
-- url     : https://prove2.me/theorems/63faaacf-f316-4a2a-ac35-43e2805a1c65
-- title:
--   Counting Sums Frames: slc gl Act
-- statement:
--   The Counting Sums Frames construction uses the slc gl Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L718-L727
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L718-L727

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

theorem Formalism.CountingSumsFrames.slc_glAct (L : Letters N) {j0 J : ℕ} (hJ : J ≤ j0) (c d : Fin r) (m : Fin N × Fin r →₀ ℕ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    slc (fsj N r j0) m (glAct p L J c d x) = glAct p L J c d (slc (fsj N r j0) m x) := by sorry
