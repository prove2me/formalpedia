-- Prove2me | Theorems.Thm_Formalism_ELL_IntegerValuedContinuity_continuous_eval
-- name    : Formalism.ELL.IntegerValuedContinuity.continuous_eval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:07.20429+00:00
-- url     : https://prove2.me/theorems/2a2a063b-6472-44a7-a332-eb6dd39b7eb8
-- title:
--   Integer Valued Continuity: continuous eval
-- statement:
--   The Integer Valued Continuity construction uses the continuous eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IntVal.lean#L7-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/IntVal.lean#L7-L15

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IntVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.IntegerValuedContinuity

theorem Formalism.ELL.IntegerValuedContinuity.continuous_eval {p : ℕ} [Fact p.Prime] {K : Type*} [NormedField K]
    [NormedAlgebra ℚ_[p] K] (P : Polynomial K) :
    Continuous fun b : ℤ_[p] => P.eval (algebraMap ℚ_[p] K (b : ℚ_[p])) := by sorry
