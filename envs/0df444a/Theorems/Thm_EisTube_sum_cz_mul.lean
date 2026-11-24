-- Prove2me | Theorems.Thm_EisTube_sum_cz_mul
-- name    : EisTube.sum_cz_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:44.192723+00:00
-- url     : https://prove2.me/theorems/3d2677a8-49c0-4989-855b-af3f4dbde524
-- title:
--   Eis Tube: sum cz mul
-- statement:
--   The Eis Tube construction uses the sum cz mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/TubeDomainExtension/TubeExtendsFarCone.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/TubeDomainExtension/TubeExtendsFarCone.lean#L28-L32

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

theorem EisTube.sum_cz_mul (x y t : ι → ℝ) :
    ∑ i, cz x y i * (t i : ℂ) =
      ((∑ i, x i * t i : ℝ) : ℂ) + ((∑ i, y i * t i : ℝ) : ℂ) * Complex.I := by sorry
