-- Prove2me | Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_subst_mem
-- name    : Formalism.MainNotions.FormalGroupSystem.Pf.Gen.subst_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:02:46.726019+00:00
-- url     : https://prove2.me/theorems/2c7f4911-fb2e-4a4d-b838-4bf8622f0991
-- title:
--   Gen: subst mem
-- statement:
--   The Gen construction uses the subst mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/JpSubstExpand.lean#L69-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/JpSubstExpand.lean#L69-L87

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

theorem Formalism.MainNotions.FormalGroupSystem.Pf.Gen.subst_mem {τ : Type} {π : σ → Pl} {π' : τ → Pl} {v : Pl} {a : σ → MvPowerSeries τ R}
    (ha : MvPowerSeries.HasSubst a) {f : MvPowerSeries σ R} (hf : f ∈ SuppOn π v)
    (h : ∀ s, π s = v → a s ∈ SuppOn π' v) : MvPowerSeries.subst a f ∈ SuppOn π' v := by sorry
