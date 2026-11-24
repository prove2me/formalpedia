-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_rowDiv_mul
-- name    : Formalism.InvariantFactorPaths.INST.rgl_rowDiv_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:33.349466+00:00
-- url     : https://prove2.me/theorems/40d202b9-7929-40af-aa17-f7beb412d5af
-- title:
--   INST: rgl row Div mul
-- statement:
--   The INST construction uses the rgl row Div mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/GlFirstLineDividedPowers.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/GlFirstLineDividedPowers.lean#L39-L42

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

theorem Formalism.InvariantFactorPaths.INST.rgl_rowDiv_mul (a b : Fin r) (k : ℕ) (f g : MvPolynomial (Fin r × Fin n) R) :
    rowDiv R a b k (f * g) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, rowDiv R a b ij.1 f * rowDiv R a b ij.2 g := by sorry
