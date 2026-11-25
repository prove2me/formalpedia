-- Prove2me | Theorems.Thm_CompanionTheory_CapEig_qminorOp_cast
-- name    : CompanionTheory.CapEig.qminorOp_cast
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:42:37.546546+00:00
-- url     : https://prove2.me/theorems/84fc4038-1555-45a2-b823-facd2fd66a2a
-- title:
--   Cap Eig: qminor Op cast
-- statement:
--   The Cap Eig construction uses the qminor Op cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/CoefEig.lean#L40-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/CoefEig.lean#L40-L46

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_FunAct
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_CoefEig
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PI.UpqRep Formalism.FourierDecayAlt
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.CapEig

theorem CompanionTheory.CapEig.qminorOp_cast {n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)) (h : m = n)
    (a : Fin m → Fin n) (ha : ∀ j, (a j).val = j.val) (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Formalism.QuantumDeterminants.qminorOp Eop a a u f = Formalism.QuantumDeterminants.qminorOp Eop id id u f := by sorry
