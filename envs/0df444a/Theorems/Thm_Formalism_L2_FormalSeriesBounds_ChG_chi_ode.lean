-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_ChG_chi_ode
-- name    : Formalism.L2.FormalSeriesBounds.ChG.chi_ode
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-27T05:26:00.991473+00:00
-- url     : https://prove2.me/theorems/b9174fed-dda3-58db-b3b3-f6f41d73fe7d
-- title:
--   Ch G: chi ode
-- statement:
--   The Ch G construction uses the chi ode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstantCoeffPderivUncurry.lean#L98-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstantCoeffPderivUncurry.lean#L98-L165

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieChar
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MfactMulCoeffMvExpLinF
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffPderivUncurry
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
open Formalism.L2.FormalSeriesBounds.ChG
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd)
open VP

theorem Formalism.L2.FormalSeriesBounds.ChG.chi_ode {χ : PS C 1 dd} (hχ : Y.IsChar χ) (i : Fin dd) :
    MvPowerSeries.pderiv C i (Psi Y χ) = Psi Y χ * MvPowerSeries.C (dlogC χ i) := by sorry
