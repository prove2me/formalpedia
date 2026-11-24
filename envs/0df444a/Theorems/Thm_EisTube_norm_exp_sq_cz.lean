-- Prove2me | Theorems.Thm_EisTube_norm_exp_sq_cz
-- name    : EisTube.norm_exp_sq_cz
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:01.946957+00:00
-- url     : https://prove2.me/theorems/d7c19112-a3a1-4c96-bec3-572d141e6a8b
-- title:
--   Eis Tube: norm exp sq cz
-- statement:
--   The Eis Tube construction uses the norm exp sq cz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/TubeDomainExtension/TubeExtendsFarCone.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/TubeDomainExtension/TubeExtendsFarCone.lean#L34-L40

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

theorem EisTube.norm_exp_sq_cz (x y : ι → ℝ) :
    ‖Complex.exp (∑ i, cz x y i ^ 2)‖ =
      Real.exp (∑ i, x i ^ 2) * Real.exp (-∑ i, y i ^ 2) := by sorry
