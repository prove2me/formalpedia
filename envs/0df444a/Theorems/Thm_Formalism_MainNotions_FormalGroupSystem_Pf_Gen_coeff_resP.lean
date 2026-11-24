-- Prove2me | Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_Gen_coeff_resP
-- name    : Formalism.MainNotions.FormalGroupSystem.Pf.Gen.coeff_resP
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T09:54:20.37932+00:00
-- url     : https://prove2.me/theorems/aeeb28fc-723a-4831-b579-85edc2e2c0dc
-- title:
--   Gen: coeff res P
-- statement:
--   The Gen construction uses the coeff res P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/JpSubstExpand.lean#L100-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/JpSubstExpand.lean#L100-L101

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

theorem Formalism.MainNotions.FormalGroupSystem.Pf.Gen.coeff_resP {R Pl : Type} [CommRing R] {ι : Pl → Type} (v : Pl) (f : MvPowerSeries (Σ v, ι v) R) (m : ι v →₀ ℕ) :
    MvPowerSeries.coeff m (resP v f) = MvPowerSeries.coeff (Finsupp.embDomain (Function.Embedding.sigmaMk v) m) f := by sorry
