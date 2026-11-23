-- Prove2me | Theorems.Thm_Formalism_DivisionValues_absE_dsum_le
-- name    : Formalism.DivisionValues.absE_dsum_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:27:22.879411+00:00
-- url     : https://prove2.me/theorems/ac0e72ac-df2c-4811-b95e-26a1f08af665
-- title:
--   Division Values: abs E dsum le
-- statement:
--   The Division Values construction uses the abs E dsum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AbsorbE.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AbsorbE.lean#L15-L22

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_StatementE
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AbsorbE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.DivisionValues

theorem Formalism.DivisionValues.absE_dsum_le {J Pl : Type} [Fintype J] [Fintype Pl] (g : J → Pl → ℝ) (c m f : ℝ)
    (hc : 0 ≤ c) (hJ : (Fintype.card J : ℝ) = m) (hP : (Fintype.card Pl : ℝ) ≤ f)
    (hg : ∀ j ρ, g j ρ ≤ c) : ∑ j, ∑ ρ, g j ρ ≤ m * (f * c) := by sorry
