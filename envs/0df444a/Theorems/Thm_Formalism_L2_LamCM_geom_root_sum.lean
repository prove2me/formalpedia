-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_geom_root_sum
-- name    : Formalism.L2.LamCM.geom_root_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:14.747443+00:00
-- url     : https://prove2.me/theorems/0ef95da4-8935-4439-a0b9-ff69dd2aa140
-- title:
--   Lam CM: geom root sum
-- statement:
--   The Lam CM construction uses the geom root sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormSpanGalois.lean#L222-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormSpanGalois.lean#L222-L239

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CoeffMemOfLoc
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormSpanGalois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

theorem Formalism.L2.LamCM.geom_root_sum {ζ : ℂ} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) {a b : ℕ} (ha : a < N) (hb : b < N) :
    ∑ j ∈ Finset.range N, (ζ ^ a * ζ⁻¹ ^ b) ^ j = if a = b then (N : ℂ) else 0 := by sorry
