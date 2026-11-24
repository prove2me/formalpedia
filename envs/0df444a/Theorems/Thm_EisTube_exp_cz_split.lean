-- Prove2me | Theorems.Thm_EisTube_exp_cz_split
-- name    : EisTube.exp_cz_split
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:23.631571+00:00
-- url     : https://prove2.me/theorems/9c27d46f-c304-42af-b0a3-4b864b43ea0e
-- title:
--   Eis Tube: exp cz split
-- statement:
--   The Eis Tube construction uses the exp cz split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/TubeDomainExtension/TubeExtendsFarCone.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/TubeDomainExtension/TubeExtendsFarCone.lean#L60-L67

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

theorem EisTube.exp_cz_split (x y t : ι → ℝ) :
    Complex.exp (2 * (Real.pi : ℂ) * ∑ i, cz x y i * t i) =
      Complex.exp (2 * (Real.pi : ℂ) * ∑ i, ((x i : ℂ)) * t i) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ∑ i, (y i : ℂ) * t i) := by sorry
