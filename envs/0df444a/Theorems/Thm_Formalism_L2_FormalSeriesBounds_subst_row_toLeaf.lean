-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_row_toLeaf
-- name    : Formalism.L2.FormalSeriesBounds.subst_row_toLeaf
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:01:24.467192+00:00
-- url     : https://prove2.me/theorems/cfeb7591-ddb7-50ce-a32a-7ee1b2000d68
-- title:
--   Formal Series Bounds: subst row to Leaf
-- statement:
--   The Formal Series Bounds construction uses the subst row to Leaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L368-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L368-L389

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
variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {ι ι' : Type} [Fintype ι]
  [Fintype ι']

theorem Formalism.L2.FormalSeriesBounds.subst_row_toLeaf {V : VF C} {d : ℕ} {J : Fin 2 → Type} (G : ∀ g, Cart V d (I g) (J g))
    (g : Fin 2) (a a' : ZMod d) (e : ι → I g → C) (v' : ι' → I (1 - g) → C)
    (he : ∀ c x, (G g).ty (Sum.inl x) ≠ a → e c x = 0)
    (hv : ∀ b x, (G (1 - g)).ty (Sum.inl x) ≠ a' → v' b x = 0) (F : MvPowerSeries (WV I) C) :
    subst (linS (rowM g e v')) (toLeaf G g a a' F) = subst (linS (rowM g e v')) F := by sorry
