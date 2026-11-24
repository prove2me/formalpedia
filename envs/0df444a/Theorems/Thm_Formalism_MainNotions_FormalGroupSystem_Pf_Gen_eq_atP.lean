-- Prove2me | Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_eq_atP
-- name    : Formalism.MainNotions.FormalGroupSystem.Pf.Gen.eq_atP
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T09:53:57.239877+00:00
-- url     : https://prove2.me/theorems/30073e6d-f27e-42bf-9cba-3fb8fbd6b7f7
-- title:
--   Gen: eq at P
-- statement:
--   The Gen construction uses the eq at P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/JpSubstExpand.lean#L103-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/JpSubstExpand.lean#L103-L136

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

theorem Formalism.MainNotions.FormalGroupSystem.Pf.Gen.eq_atP {R Pl : Type} [CommRing R] {ι : Pl → Type} [Fintype Pl] [DecidableEq Pl] (v : Pl)
    (f : MvPowerSeries (Σ v, ι v) R) (hf : f ∈ SuppOn (Sigma.fst : (Σ v, ι v) → Pl) v) :
    f = atP v (resP v f) := by sorry
