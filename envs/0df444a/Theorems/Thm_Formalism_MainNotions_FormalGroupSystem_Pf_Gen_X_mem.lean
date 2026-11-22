-- Prove2me | Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_X_mem
-- name    : Formalism.MainNotions.FormalGroupSystem.Pf.Gen.X_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:02:53.67702+00:00
-- url     : https://prove2.me/theorems/a549af81-abd0-49f8-88a9-dd563ababcd5
-- title:
--   Gen: X mem
-- statement:
--   The Gen construction uses the X mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/JpSubstExpand.lean#L49-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/JpSubstExpand.lean#L49-L58

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_CoeffProdRename
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_JpSubstExpand
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
variable {R σ Pl : Type} [CommRing R]

theorem Formalism.MainNotions.FormalGroupSystem.Pf.Gen.X_mem {π : σ → Pl} {v : Pl} {x : σ} (h : π x = v) : (MvPowerSeries.X x : MvPowerSeries σ R) ∈ SuppOn π v := by sorry
