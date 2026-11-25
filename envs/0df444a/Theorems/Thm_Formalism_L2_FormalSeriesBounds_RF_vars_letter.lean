-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_vars_letter
-- name    : Formalism.L2.FormalSeriesBounds.RF.vars_letter
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:13:50.055834+00:00
-- url     : https://prove2.me/theorems/b195309a-b1c2-4141-b152-3ea13c1e755a
-- title:
--   RF: vars letter
-- statement:
--   The RF construction uses the vars letter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAdm.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAdm.lean#L47-L52

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAdm
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
open Formalism.IncomingBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
  (X : RowData C V d I J) (F : Flag X)

theorem Formalism.L2.FormalSeriesBounds.RF.vars_letter {g : Fin 2} {a : ZMod d} {N : ℕ} {Q : MvPolynomial (Fin N × Fin (X.rkF g a)) C} {ρ : Fin N} {w : WV I}
    (h : (ρ, w) ∈ (MvPolynomial.rename (F.letter g a) Q).vars) : w.1 = g ∧ tyW X.G w = a := by sorry
