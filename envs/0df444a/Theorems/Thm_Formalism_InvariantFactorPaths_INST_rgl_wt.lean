-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_wt
-- name    : Formalism.InvariantFactorPaths.INST.rgl_wt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:01.695532+00:00
-- url     : https://prove2.me/theorems/4991e8d1-0dfd-4e2a-a483-482ac5336dbd
-- title:
--   INST: rgl wt
-- statement:
--   The INST construction uses the rgl wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/GlFirstLineDividedPowers.lean#L100-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/GlFirstLineDividedPowers.lean#L100-L106

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_GlFirstLineDividedPowers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.INST
open Formalism.GradedWeylDivisibility Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.InvariantFactorPaths.PW
variable {p : ℕ} [Fact p.Prime] {r n : ℕ}

theorem Formalism.InvariantFactorPaths.INST.rgl_wt (ν : Fin n → ℕ) (a : Fin r) (m : Fin r × Fin n →₀ ℕ) :
    wt (vecL ν) n a (Finsupp.mapDomain (Equiv.prodComm (Fin r) (Fin n)) m) = (rowDeg m a : ℤ) := by sorry
