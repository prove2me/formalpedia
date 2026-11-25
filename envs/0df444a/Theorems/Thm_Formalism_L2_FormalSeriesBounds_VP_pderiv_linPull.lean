-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_pderiv_linPull
-- name    : Formalism.L2.FormalSeriesBounds.VP.pderiv_linPull
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:20:46.191325+00:00
-- url     : https://prove2.me/theorems/0ec6a91d-0bdb-5e40-ac11-5b1c45f64425
-- title:
--   VP: pderiv lin Pull
-- statement:
--   The VP construction uses the pderiv lin Pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValG.lean#L62-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValG.lean#L62-L75

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValG
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {Var : Type} [Fintype Var] {n : ℕ}
variable (Y : FBChart C V O dd) (M : Var → Fin n × Fin dd → C)

theorem Formalism.L2.FormalSeriesBounds.VP.pderiv_linPull (x : Var) (F : PS C n dd) :
    MvPowerSeries.pderiv C x (linPull Y M F) =
      ∑ b, ∑ j, (∑ i, MvPowerSeries.C (M x (b, i)) * RR Y M b i j) *
        linPull Y M (MvPowerSeries.pderiv C (b, j) F) := by sorry
