-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RowData_hPull_axis_left
-- name    : Formalism.L2.FormalSeriesBounds.RowData.hPull_axis_left
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:44:49.595775+00:00
-- url     : https://prove2.me/theorems/5fef587e-c86f-4711-855e-68587f2b4281
-- title:
--   Row Data: h Pull axis left
-- statement:
--   The Row Data construction uses the h Pull axis left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L759-L775
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L759-L775

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
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
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (Xr : RowData C V d I J) {ι ι' : Type} [Fintype ι]
  [Fintype ι']

theorem Formalism.L2.FormalSeriesBounds.RowData.hPull_axis_left (g : Fin 2) (a a' : ZMod d) (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) (A : ι ⊕ ι' →₀ ℕ) (hA : ∀ c, A (Sum.inl c) = 0) :
    coeff A (hPullW (Xr.hL g a a') (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b))) = 0 := by sorry
