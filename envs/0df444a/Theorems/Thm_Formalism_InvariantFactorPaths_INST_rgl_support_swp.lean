-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_support_swp
-- name    : Formalism.InvariantFactorPaths.INST.rgl_support_swp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:17.878564+00:00
-- url     : https://prove2.me/theorems/bbc58791-c7c3-4b4d-9d30-659b973fce16
-- title:
--   INST: rgl support swp
-- statement:
--   The INST construction uses the rgl support swp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/GlFirstLineDividedPowers.lean#L77-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/GlFirstLineDividedPowers.lean#L77-L80

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
variable (R : Type) [CommRing R] {r n : ℕ}

theorem Formalism.InvariantFactorPaths.INST.rgl_support_swp (f : MvPolynomial (Fin r × Fin n) R) :
    (swp R r n f).support =
      f.support.image (Finsupp.mapDomain (Equiv.prodComm (Fin r) (Fin n))) := by sorry
