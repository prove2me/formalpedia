-- Prove2me | Theorems.Thm_CompanionTheory_CapEig_inUJ_one
-- name    : CompanionTheory.CapEig.inUJ_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:54:30.730868+00:00
-- url     : https://prove2.me/theorems/a6cefd2b-c0e8-40f3-84a6-e956d6b4d744
-- title:
--   Cap Eig: in UJ one
-- statement:
--   The Cap Eig construction uses the in UJ one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/FunAct.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/FunAct.lean#L33-L34

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_Transport
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_FunAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants PI.DSInfCharCap
noncomputable section
open CompanionTheory CompanionTheory.CapEig
variable {n : ℕ} {ε : Fin n → Bool} {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {σ : Matrix (Fin n) (Fin n) ℂ → (Hs →L[ℂ] Hs)}

theorem CompanionTheory.CapEig.inUJ_one : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by sorry
