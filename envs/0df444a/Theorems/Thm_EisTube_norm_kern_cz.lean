-- Prove2me | Theorems.Thm_EisTube_norm_kern_cz
-- name    : EisTube.norm_kern_cz
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:21:33.855922+00:00
-- url     : https://prove2.me/theorems/1d39bd67-6b0e-430b-b0b3-c3a41e71be34
-- title:
--   Eis Tube: norm kern cz
-- statement:
--   The Eis Tube construction uses the norm kern cz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/TubeDomainExtension/TubeExtendsFarCone.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/TubeDomainExtension/TubeExtendsFarCone.lean#L45-L49

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Statement
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_Lemmas
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_TubeDomainExtension_TubeExtendsFarCone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory
open EisTube
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
variable {ι : Type} [Fintype ι]

theorem EisTube.norm_kern_cz (x y t : ι → ℝ) :
    ‖kern (cz x y) t‖ = Real.exp (-(2 * Real.pi * ∑ i, x i * t i)) := by sorry
