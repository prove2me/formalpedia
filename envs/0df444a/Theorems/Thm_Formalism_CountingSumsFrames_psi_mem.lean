-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_psi_mem
-- name    : Formalism.CountingSumsFrames.psi_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:45:45.427105+00:00
-- url     : https://prove2.me/theorems/41f60229-d273-419c-adcf-621310047be5
-- title:
--   Counting Sums Frames: psi mem
-- statement:
--   The Counting Sums Frames construction uses the psi mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L945-L946
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L945-L946

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

theorem Formalism.CountingSumsFrames.psi_mem (L : Letters N) (j0 : ℕ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) : psi p L j0 x ∈ Pol p r (Lz L j0) := by sorry
