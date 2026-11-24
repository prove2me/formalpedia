-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_monomial_mem_pol
-- name    : Formalism.InvariantFactorPaths.PW.monomial_mem_pol
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:55.609803+00:00
-- url     : https://prove2.me/theorems/adcdf420-5996-42c5-b1b9-ac07ab011721
-- title:
--   PW: monomial mem pol
-- statement:
--   The PW construction uses the monomial mem pol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeightCompApply.lean#L277-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeightCompApply.lean#L277-L286

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_HasLatBasis
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}

theorem Formalism.InvariantFactorPaths.PW.monomial_mem_pol (LL : Letters N) (m : Fin N × Fin r →₀ ℕ) (a : ℚ_[p]) :
    monomial m a ∈ Pol p r (⟨LL.vec, fun i => ∑ c, m (i, c)⟩ : Letters N) := by sorry
