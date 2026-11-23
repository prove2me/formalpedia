-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_A2_gramC_eq
-- name    : Formalism.L2.LamCM.A2.gramC_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:38.778138+00:00
-- url     : https://prove2.me/theorems/c1d1ebde-e15a-42dc-93b5-6f07fbe3b47d
-- title:
--   A2: gram C eq
-- statement:
--   The A2 construction uses the gram C eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L195-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ProdMulLeDetIdeal.lean#L195-L201

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ProdMulLeDetIdeal
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
open scoped nonZeroDivisors ComplexOrder
open Formalism.L2.LamCM.A2
variable {K : Type} [Field K] [NumberField K]

theorem Formalism.L2.LamCM.A2.gramC_eq {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) (b : Fin n → Fin n → K) :
    ReciprocityTheory.MultiplicativeHeights.gramC H σ b = ((Matrix.of b).map σ).transpose.conjTranspose * H * ((Matrix.of b).map σ).transpose := by sorry
