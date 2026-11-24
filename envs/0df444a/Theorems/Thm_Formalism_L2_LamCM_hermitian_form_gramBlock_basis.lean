-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_hermitian_form_gramBlock_basis
-- name    : Formalism.L2.LamCM.hermitian_form_gramBlock_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:04.321578+00:00
-- url     : https://prove2.me/theorems/f37baa81-dc92-4b9f-9995-f7fdb9ec4bf5
-- title:
--   Lam CM: hermitian form gram Block basis
-- statement:
--   The Lam CM construction uses the hermitian form gram Block basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/HermitianFormGramBlockBasis.lean#L45-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/HermitianFormGramBlockBasis.lean#L45-L50

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
variable {K : Type} [Field K] [NumberField K] {B : Type} {m : B → ℕ} {g : ℕ}

theorem Formalism.L2.LamCM.hermitian_form_gramBlock_basis (e : (Σ b, Fin (m b)) ≃ Fin g) (U : Matrix (Fin g) (Fin g) K) (H : Matrix (Fin g) (Fin g) ℂ)
    (σ : K →+* ℂ) (b : B) (j : Fin (m b)) :
    ReciprocityTheory.MultiplicativeHeights.hq (gramBlock e U H σ b) ((1 : Matrix (Fin (m b)) (Fin (m b)) ℂ) j) =
      ReciprocityTheory.MultiplicativeHeights.hq H (ReciprocityTheory.MultiplicativeHeights.embVec σ (U (e ⟨b, j⟩))) := by sorry
