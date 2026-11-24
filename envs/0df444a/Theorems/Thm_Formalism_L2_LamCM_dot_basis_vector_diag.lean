-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_dot_basis_vector_diag
-- name    : Formalism.L2.LamCM.dot_basis_vector_diag
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:24.323261+00:00
-- url     : https://prove2.me/theorems/201a4ce1-f4ab-4096-8ffd-528c483113e6
-- title:
--   Lam CM: dot basis vector diag
-- statement:
--   The Lam CM construction uses the dot basis vector diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/HermitianFormGramBlockBasis.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/HermitianFormGramBlockBasis.lean#L13-L15

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementS
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_FiniteDetAddSmulOneEqZero
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_LargeResidueExtensionLemma
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_HermitianFormGramBlockBasis
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
open NumberField IsDedekindDomain IsLocalRing Matrix
open scoped nonZeroDivisors ComplexOrder

theorem Formalism.L2.LamCM.dot_basis_vector_diag {k : ℕ} (M : Matrix (Fin k) (Fin k) ℂ) (j : Fin k) :
    star ((1 : Matrix (Fin k) (Fin k) ℂ) j) ⬝ᵥ (M *ᵥ (1 : Matrix (Fin k) (Fin k) ℂ) j) = M j j := by sorry
