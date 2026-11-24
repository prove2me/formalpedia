-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_gramBlock_eq
-- name    : Formalism.L2.LamCM.gramBlock_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:54.994427+00:00
-- url     : https://prove2.me/theorems/3a5a19c1-d7c8-4f3e-a00d-0c96bd295c9e
-- title:
--   Lam CM: gram Block eq
-- statement:
--   The Lam CM construction uses the gram Block eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/HermitianFormGramBlockBasis.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/HermitianFormGramBlockBasis.lean#L21-L27

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

theorem Formalism.L2.LamCM.gramBlock_eq (e : (Σ b, Fin (m b)) ≃ Fin g) (U : Matrix (Fin g) (Fin g) K) (H : Matrix (Fin g) (Fin g) ℂ)
    (σ : K →+* ℂ) (b : B) :
    gramBlock e U H σ b = (((U.map σ).submatrix (fun j => e ⟨b, j⟩) id)ᵀ)ᴴ * H *
      ((U.map σ).submatrix (fun j => e ⟨b, j⟩) id)ᵀ := by sorry
