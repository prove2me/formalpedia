-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_lg_addOf
-- name    : Formalism.L2.FormalSeriesBounds.lg_addOf
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T05:19:49.281811+00:00
-- url     : https://prove2.me/theorems/5fd7c94c-b18d-5896-b5a8-a7fc7f0804f4
-- title:
--   Formal Series Bounds: lg add Of
-- statement:
--   The Formal Series Bounds construction uses the lg add Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L206-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L206-L229

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerate
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem Formalism.L2.FormalSeriesBounds.lg_addOf (Y : FBChart C V O dd) {τ : Type} (P : Fin 2 → Fin dd → MvPowerSeries τ C)
    (hP : ∀ k j, MvPowerSeries.constantCoeff (P k j) = 0) (i : Fin dd) :
    MvPowerSeries.subst (fun j => MvPowerSeries.subst (fun q : Fin 2 × Fin dd => P q.1 q.2) (Y.B.G.F j))
        (un1 (Y.lg i)) =
      MvPowerSeries.subst (P 0) (un1 (Y.lg i)) + MvPowerSeries.subst (P 1) (un1 (Y.lg i)) := by sorry
