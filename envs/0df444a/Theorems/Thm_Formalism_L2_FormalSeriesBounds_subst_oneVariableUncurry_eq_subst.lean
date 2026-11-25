-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_oneVariableUncurry_eq_subst
-- name    : Formalism.L2.FormalSeriesBounds.subst_oneVariableUncurry_eq_subst
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:38:22.924329+00:00
-- url     : https://prove2.me/theorems/cfce6526-13d3-49bd-9976-9b358adcedf8
-- title:
--   Formal Series Bounds: subst one Variable Uncurry eq subst
-- statement:
--   The Formal Series Bounds construction uses the subst one Variable Uncurry eq subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieCartFB.lean#L70-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieCartFB.lean#L70-L77

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable {dd : ℕ}

theorem Formalism.L2.FormalSeriesBounds.subst_oneVariableUncurry_eq_subst {σ : Type} [Finite σ] {b : σ → PS C 1 dd} (hb : ∀ s, MvPowerSeries.constantCoeff (b s) = 0)
    (f : MvPowerSeries σ C) :
    un1 (MvPowerSeries.subst b f) = MvPowerSeries.subst (fun s => un1 (b s)) f := by sorry
