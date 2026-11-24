-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_swp_map
-- name    : Formalism.InvariantFactorPaths.INST.rgl_swp_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:51.660806+00:00
-- url     : https://prove2.me/theorems/cc096dcf-d7b1-41d5-929d-6b15017bb4fb
-- title:
--   INST: rgl swp map
-- statement:
--   The INST construction uses the rgl swp map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/GlFirstLineDividedPowers.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/GlFirstLineDividedPowers.lean#L26-L28

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

theorem Formalism.InvariantFactorPaths.INST.rgl_swp_map {S : Type} [CommRing S] (φ : R →+* S) (f : MvPolynomial (Fin r × Fin n) R) :
    swp S r n (map φ f) = map φ (swp R r n f) := by sorry
