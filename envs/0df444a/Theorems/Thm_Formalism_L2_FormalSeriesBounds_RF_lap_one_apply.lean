-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_lap_one_apply
-- name    : Formalism.L2.FormalSeriesBounds.RF.lap_one_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:47:16.595283+00:00
-- url     : https://prove2.me/theorems/f2af4a84-11ee-4d1c-8d85-a90816727576
-- title:
--   RF: lap one apply
-- statement:
--   The RF construction uses the lap one apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/FinTwoNeOneSub.lean#L195-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/FinTwoNeOneSub.lean#L195-L200

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FinTwoNeOneSub
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
open Formalism.IncomingBounds Formalism.L2.Pj

theorem Formalism.L2.FormalSeriesBounds.RF.lap_one_apply {T : Type} (r : T → ℕ) (n : ℕ) (C : Type) [Field C] (τ τ' : T) (a : Fin (r τ)) (a' : Fin (r τ'))
    (P : MvPolynomial (Letter T r n) C) :
    lap r n C 1 τ τ' a a' P = ∑ b, ∑ b', (1 : Matrix (Fin n) (Fin n) C) b b' •
      MvPolynomial.pderiv (⟨τ, a, b⟩ : Letter T r n) (MvPolynomial.pderiv (⟨τ', a', b'⟩ : Letter T r n) P) := by sorry
