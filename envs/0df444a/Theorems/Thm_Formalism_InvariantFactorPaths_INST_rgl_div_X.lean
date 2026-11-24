-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_INST_rgl_div_X
-- name    : Formalism.InvariantFactorPaths.INST.rgl_div_X
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:36:14.692846+00:00
-- url     : https://prove2.me/theorems/e4984cd8-cc0f-4238-9127-cae086148ccd
-- title:
--   INST: rgl div X
-- statement:
--   The INST construction uses the rgl div X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/GlFirstLineDividedPowers.lean#L108-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/SandwichModelDomains/SandwichModelProofs/GlFirstLineDividedPowers.lean#L108-L119

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

theorem Formalism.InvariantFactorPaths.INST.rgl_div_X (ν : Fin n → ℕ) (a b : Fin r) (hab : a ≠ b) (k : ℕ) (v : Fin r × Fin n) :
    swp ℚ_[p] r n (rowDiv ℚ_[p] a b k (X v)) =
      ((k.factorial : ℚ_[p]))⁻¹ • ((glAct p (vecL ν) n a b) ^ k) (swp ℚ_[p] r n (X v)) := by sorry
