-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_sys_curve
-- name    : Formalism.L2.FormalSeriesBounds.FormalGermZero.sys_curve
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:54:39.215281+00:00
-- url     : https://prove2.me/theorems/a92eb960-f203-4226-b458-fef96ebe63a6
-- title:
--   Formal Germ Zero: sys curve
-- statement:
--   The Formal Germ Zero construction uses the sys curve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffSingleSubstOfLowDegree.lean#L400-L406
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffSingleSubstOfLowDegree.lean#L400-L406

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

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
open Formalism.L2.FormalSeriesBounds.FormalGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)]

theorem Formalism.L2.FormalSeriesBounds.FormalGermZero.sys_curve (Y : FBChart C V O dd) (p : PairData Y d I) {g : Fin 2} (hg : (Y.raw p).CartHyp V g)
    (S : Sys (RawChart.cart hg)) (c : I g) :
    ∃ γ : Fin dd → PowerSeries C, IsCv V γ ∧ ∀ i, MvPowerSeries.subst γ (un1 (Y.lg i)) =
      ∑ c' : I g, p.u g c' i • tyS V.l (fun s => S.al c s c') := by sorry
