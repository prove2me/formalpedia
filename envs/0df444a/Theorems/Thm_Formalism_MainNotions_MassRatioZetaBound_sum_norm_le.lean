-- Prove2me | Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_sum_norm_le
-- name    : Formalism.MainNotions.MassRatioZetaBound.sum_norm_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:06.117905+00:00
-- url     : https://prove2.me/theorems/5ce8400f-d81e-4078-8976-4d573f3b760c
-- title:
--   Mass Ratio Zeta Bound: sum norm le
-- statement:
--   The Mass Ratio Zeta Bound construction uses the sum norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/MassRatioBound.lean#L87-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/MassRatioBound.lean#L87-L116

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.MassRatioZetaBound
open NumberField
variable {K : Type*} [Field K] [NumberField K]

theorem Formalism.MainNotions.MassRatioZetaBound.sum_norm_le (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, P.IsMaximal) :
    ∑ P ∈ S, 1 / ((Ideal.absNorm P : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ (Module.finrank ℚ K : ℝ) * zetaGL3GL2 := by sorry
