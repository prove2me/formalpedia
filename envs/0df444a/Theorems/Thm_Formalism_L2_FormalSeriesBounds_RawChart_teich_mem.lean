-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_teich_mem
-- name    : Formalism.L2.FormalSeriesBounds.RawChart.teich_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:14:30.93284+00:00
-- url     : https://prove2.me/theorems/e516fd26-1228-4438-a334-2e2df7635698
-- title:
--   Raw Chart: teich mem
-- statement:
--   The Raw Chart construction uses the teich mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstMemTypeSetOfNonneg.lean#L176-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstMemTypeSetOfNonneg.lean#L176-L185

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstMemTypeSetOfNonneg
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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
open Formalism.L2.FormalSeriesBounds.RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem Formalism.L2.FormalSeriesBounds.RawChart.teich_mem (V : VF C) (g : Fin 2) (c : C) (hc : V.Ge 0 c) (x : ℕ → I g ⊕ JJ I g → C)
    (hx : x ∈ X.TySet V g) : teich V.l c x ∈ X.TySet V g := by sorry
