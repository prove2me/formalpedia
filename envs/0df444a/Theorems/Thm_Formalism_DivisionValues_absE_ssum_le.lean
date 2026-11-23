-- Prove2me | Theorems.Thm_Formalism_DivisionValues_absE_ssum_le
-- name    : Formalism.DivisionValues.absE_ssum_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:05:05.905797+00:00
-- url     : https://prove2.me/theorems/9c66df75-6a4f-4e07-8be4-814764b94814
-- title:
--   Division Values: abs E ssum le
-- statement:
--   The Division Values construction uses the abs E ssum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AbsorbE.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/AbsorbE.lean#L10-L13

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

theorem Formalism.DivisionValues.absE_ssum_le {J : Type} [Fintype J] (g : J → ℝ) (c m : ℝ)
    (hJ : (Fintype.card J : ℝ) = m) (hg : ∀ j, g j ≤ c) : ∑ j, g j ≤ m * c := by sorry
