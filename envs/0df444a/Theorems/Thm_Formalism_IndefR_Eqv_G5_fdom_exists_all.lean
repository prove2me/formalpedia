-- Prove2me | Theorems.Thm_Formalism_IndefR_Eqv_G5_fdom_exists_all
-- name    : Formalism.IndefR.Eqv.G5.fdom_exists_all
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:31.365826+00:00
-- url     : https://prove2.me/theorems/b84e6343-1b4b-4c50-b314-ec0090b54c4b
-- title:
--   G5: fdom exists all
-- statement:
--   The G5 construction uses the fdom exists all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/FdomExistsAll.lean#L8-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/FdomExistsAll.lean#L8-L12

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasB_Imports
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_FdomExistsAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open Formalism Formalism.IndefR Formalism.IndefR.Eqv Formalism.IndefR.Eqv.G5

theorem Formalism.IndefR.Eqv.G5.fdom_exists_all {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] :
    ∃ s : Set G, MeasurableSet s ∧ ∀ μ : Measure G, IsFundamentalDomain Γ s μ := by sorry
