-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_lix_locP
-- name    : Formalism.EigenvalueLevelCeiling.lix_locP
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:04.115782+00:00
-- url     : https://prove2.me/theorems/f195395f-0d70-4138-bfce-f0558558c6b0
-- title:
--   Eigenvalue Level Ceiling: lix loc P
-- statement:
--   The Eigenvalue Level Ceiling construction uses the lix loc P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/LocalConditionsWeightedConditional.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/LocalConditionsWeightedConditional.lean#L69-L73

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementLoc
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsWeightedConditional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues Formalism.HermitianLatticesTheory
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.EigenvalueLevelCeiling.lix_locP {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] (w : HeightOneSpectrum (𝓞 K))
    (A B : Submodule (𝓞 K) Z) :
    lix w A B = lix w (localization₂ w.asIdeal A) (localization₂ w.asIdeal B) := by sorry
