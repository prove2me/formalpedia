-- Prove2me | Theorems.Thm_Formalism_DivisionValues_inv_inv_real_smul
-- name    : Formalism.DivisionValues.inv_inv_real_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:08:12.039478+00:00
-- url     : https://prove2.me/theorems/b94f0129-7202-47c8-abce-c9aa7aac3bd5
-- title:
--   Division Values: inv inv real smul
-- statement:
--   The Division Values construction uses the inv inv real smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/KappaNormalise.lean#L173-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/KappaNormalise.lean#L173-L179

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_PassageScaleFree
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K]

theorem Formalism.DivisionValues.inv_inv_real_smul {d : ℕ} (s : ℝ) (hs : 0 < s) (A : Matrix (Fin d) (Fin d) ℂ) (hA : IsUnit A.det) :
    (((s⁻¹ : ℝ) : ℂ) • A)⁻¹ = ((s : ℝ) : ℂ) • A⁻¹ := by sorry
