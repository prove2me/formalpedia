-- Prove2me | Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_mem_SuppOn
-- name    : Formalism.MainNotions.FormalGroupSystem.Pf.Gen.mem_SuppOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:21.634437+00:00
-- url     : https://prove2.me/theorems/d4eb8c75-6afc-4872-8a88-d53bdba6175b
-- title:
--   Gen: mem Supp On
-- statement:
--   The Gen construction uses the mem Supp On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/JpSubstExpand.lean#L46-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/JpSubstExpand.lean#L46-L47

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

theorem Formalism.MainNotions.FormalGroupSystem.Pf.Gen.mem_SuppOn {π : σ → Pl} {v : Pl} {f : MvPowerSeries σ R} :
    f ∈ SuppOn π v ↔ ∀ m, MvPowerSeries.coeff m f ≠ 0 → ∀ x ∈ m.support, π x = v := by sorry
