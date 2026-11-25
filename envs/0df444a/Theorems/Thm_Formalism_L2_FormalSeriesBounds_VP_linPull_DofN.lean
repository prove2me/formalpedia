-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_linPull_DofN
-- name    : Formalism.L2.FormalSeriesBounds.VP.linPull_DofN
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:23:01.798847+00:00
-- url     : https://prove2.me/theorems/88aa5eda-cee1-4d63-80a1-e49c5405a6f8
-- title:
--   VP: lin Pull Dof N
-- statement:
--   The VP construction uses the lin Pull Dof N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValG.lean#L55-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValG.lean#L55-L60

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

theorem Formalism.L2.FormalSeriesBounds.VP.linPull_DofN (b : Fin n) (u : Fin dd → C) (F : PS C n dd) :
    linPull Y M (DofN (Y.B.FK C) b u F) =
      ∑ j, (∑ i, MvPowerSeries.C (u i) * RR Y M b i j) * linPull Y M (MvPowerSeries.pderiv C (b, j) F) := by sorry
