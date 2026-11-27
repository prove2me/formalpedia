-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_ex_lg_at
-- name    : Formalism.L2.FormalSeriesBounds.ex_lg_at
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T05:25:12.434044+00:00
-- url     : https://prove2.me/theorems/590dcf51-68a2-47b5-8a3c-135f4ca66402
-- title:
--   Formal Series Bounds: ex lg at
-- statement:
--   The Formal Series Bounds construction uses the ex lg at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L231-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean#L231-L237

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

theorem Formalism.L2.FormalSeriesBounds.ex_lg_at (Y : FBChart C V O dd) (p : PairData Y d I) {τ : Type} (A : Fin dd → MvPowerSeries τ C)
    (hA : ∀ j, MvPowerSeries.constantCoeff (A j) = 0) (i : Fin dd) :
    MvPowerSeries.subst (fun j => MvPowerSeries.subst A ((Y.raw p).lg j)) ((Y.raw p).ex i) = A i := by sorry
