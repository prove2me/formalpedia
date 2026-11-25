-- Prove2me | Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_memLocalization_mul
-- name    : Formalism.MainNotions.FormalGroupSystem.Pf.Gen.memLocalization_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:49:44.823401+00:00
-- url     : https://prove2.me/theorems/f41b5688-9e69-42de-80a8-5da2f44ee72a
-- title:
--   Gen: mem Localization mul
-- statement:
--   The Gen construction uses the mem Localization mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/CoeffProdRename.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/CoeffProdRename.lean#L30-L32

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_CoeffProdRename
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.FormalGroupSystem.Pf Formalism.MainNotions.FormalGroupSystem.Pf.Gen
open Finset
variable {K Pl : Type} [CommRing K] {ι : Pl → Type}

theorem Formalism.MainNotions.FormalGroupSystem.Pf.Gen.memLocalization_mul (v : Pl) (f g : MvPowerSeries (ι v) K) : atP v (f * g) = atP v f * atP v g := by sorry
