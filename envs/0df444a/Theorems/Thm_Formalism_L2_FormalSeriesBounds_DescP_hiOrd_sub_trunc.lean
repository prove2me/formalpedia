-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_DescP_hiOrd_sub_trunc
-- name    : Formalism.L2.FormalSeriesBounds.DescP.hiOrd_sub_trunc
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:33:24.582724+00:00
-- url     : https://prove2.me/theorems/cb2374b2-740b-45fd-aa12-ce3b072acb9d
-- title:
--   Desc P: hi Ord sub trunc
-- statement:
--   The Desc P construction uses the hi Ord sub trunc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePDescJet.lean#L147-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePDescJet.lean#L147-L154

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDesc
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescJet
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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.DescP
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {n d : ℕ}

theorem Formalism.L2.FormalSeriesBounds.DescP.hiOrd_sub_trunc (f : PS k n d) (D : ℕ) :
    HiOrd (D + 1) (f - ((trunc' k (cst D) f : MvPolynomial _ k) : PS k n d)) := by sorry
