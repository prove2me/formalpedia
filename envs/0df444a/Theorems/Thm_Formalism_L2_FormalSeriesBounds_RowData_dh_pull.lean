-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RowData_dh_pull
-- name    : Formalism.L2.FormalSeriesBounds.RowData.dh_pull
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:44:45.357436+00:00
-- url     : https://prove2.me/theorems/8187314a-8715-41d2-9245-6898c1d6d99a
-- title:
--   Row Data: dh pull
-- statement:
--   The Row Data construction uses the dh pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L777-L844
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L777-L844

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

theorem Formalism.L2.FormalSeriesBounds.RowData.dh_pull (hAlt : Xr.Alt) (g : Fin 2) (a a' : ZMod d) (hodd : Odd (a' - a).val)
    (S : ∀ g, Sys (Xr.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C) (hT : ∀ g, (S g).IsT (t g))
    (e : ι → I g → C) (v' : ι' → I (1 - g) → C)
    (he : ∀ c x, (Xr.G g).ty (Sum.inl x) ≠ a → e c x = 0)
    (hv : ∀ b x, (Xr.G (1 - g)).ty (Sum.inl x) ≠ a' → v' b x = 0)
    (hvint : ∀ b x, V.Ge 0 (v' b x)) (b : ι') :
    ∃ Kp : MvPowerSeries (I g ⊕ I (1 - g)) C, (∀ A, V.Ge 0 (coeff A Kp)) ∧
      dVar (Sum.inr b)
          (hPullW (Xr.hL g a a') (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b))) =
        subst (ttPull t g e v') Kp +
          rename (Function.Embedding.inl : ι ↪ ι ⊕ ι')
            (∑ k : I (1 - g), v' b k • ∑ κ : J g,
              Xr.pair g κ k • subst (linS e) ((S g).ze (t g) κ)) := by sorry
