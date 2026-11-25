-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_sys_P
-- name    : Formalism.L2.FormalSeriesBounds.FormalGermZero.sys_P
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:32:57.411349+00:00
-- url     : https://prove2.me/theorems/25eb1459-4d65-42ca-b016-084e6aa93f43
-- title:
--   Formal Germ Zero: sys P
-- statement:
--   The Formal Germ Zero construction uses the sys P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffSingleSubstOfLowDegree.lean#L408-L494
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffSingleSubstOfLowDegree.lean#L408-L494

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
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

theorem Formalism.L2.FormalSeriesBounds.FormalGermZero.sys_P (Y : FBChart C V O dd) (p : PairData Y d I) {g : Fin 2} (hg : (Y.raw p).CartHyp V g)
    (S : Sys (RawChart.cart hg)) :
    ∃ P : Fin dd → MvPowerSeries (I g) C, (∀ j, MvPowerSeries.constantCoeff (P j) = 0) ∧
      (∀ j, IntS V (P j)) ∧
      (∀ j c, MvPowerSeries.coeff (Finsupp.single c 1) (P j) = ∑ c', p.u g c' j * S.tan c c') ∧
      ∀ t : I g → MvPowerSeries (I g) C, S.IsT t → ∀ j,
        MvPowerSeries.subst t (P j) =
          MvPowerSeries.subst (fun i => ∑ c', p.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C))
            ((Y.raw p).ex j) := by sorry
