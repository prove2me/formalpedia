-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_chain_aeval
-- name    : Formalism.L2.FormalSeriesBounds.RF.chain_aeval
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:47:54.529825+00:00
-- url     : https://prove2.me/theorems/dc64a296-5445-5f83-a488-014b4f9cf30a
-- title:
--   RF: chain aeval
-- statement:
--   The RF construction uses the chain aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PderivSubGOff.lean#L19-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PderivSubGOff.lean#L19-L37

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCDeg
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FinTwoNeOneSub
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PderivSubGOff
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] {r : T → ℕ} {tau : Orb → ZMod 2 → T}
  {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C} {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

theorem Formalism.L2.FormalSeriesBounds.RF.chain_aeval {σ τ : Type} [Fintype σ] (S : MvPolynomial σ C →ₐ[C] MvPolynomial τ C) (ℓ : τ) (p : MvPolynomial σ C) :
    pderiv ℓ (S p) = ∑ y, S (pderiv y p) * pderiv ℓ (S (X y)) := by sorry
