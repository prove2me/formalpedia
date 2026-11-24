-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_psi_comp
-- name    : Formalism.CountingSumsFrames.psi_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:45:58.60393+00:00
-- url     : https://prove2.me/theorems/99399b81-9db9-4ddb-b53d-8404c65e90cd
-- title:
--   Counting Sums Frames: psi comp
-- statement:
--   The Counting Sums Frames construction uses the psi comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L997-L999
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L997-L999

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

theorem Formalism.CountingSumsFrames.psi_comp (L L' : Letters N) (j0 j : ℕ) (ν : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    psi p L j0 ((GA p L' j).comp ν x) = (GA p L' j).comp ν (psi p L j0 x) := by sorry
