-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_glAct_X
-- name    : Formalism.InvariantFactorPaths.INST.rgl_glAct_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:06.730917+00:00
-- url     : https://prove2.me/theorems/0722be83-5e97-4561-acd6-25bd53b94d53
-- title:
--   INST: rgl gl Act X
-- statement:
--   The INST construction uses the rgl gl Act X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/GlFirstLineDividedPowers.lean#L95-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/GlFirstLineDividedPowers.lean#L95-L98

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

theorem Formalism.InvariantFactorPaths.INST.rgl_glAct_X (ν : Fin n → ℕ) (a b c : Fin r) (s : Fin n) :
    glAct p (vecL ν) n a b (X (s, c)) = if c = b then X (s, a) else 0 := by sorry
