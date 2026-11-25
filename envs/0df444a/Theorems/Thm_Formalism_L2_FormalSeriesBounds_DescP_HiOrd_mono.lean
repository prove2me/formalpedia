-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_DescP_HiOrd_mono
-- name    : Formalism.L2.FormalSeriesBounds.DescP.HiOrd.mono
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:33:20.339435+00:00
-- url     : https://prove2.me/theorems/73842db0-9f12-4243-867a-6131734e69a8
-- title:
--   Hi Ord: mono
-- statement:
--   The Hi Ord construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePDescJet.lean#L21-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePDescJet.lean#L21-L21

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDesc
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescJet
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mono
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mono

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

theorem Formalism.L2.FormalSeriesBounds.DescP.HiOrd.mono {K K' : ℕ} {g : PS k n d} (h : HiOrd K' g) (hK : K ≤ K') : HiOrd K g := by sorry
