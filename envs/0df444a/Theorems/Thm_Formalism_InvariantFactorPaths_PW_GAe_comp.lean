-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_GAe_comp
-- name    : Formalism.InvariantFactorPaths.PW.GAe_comp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:04.6978+00:00
-- url     : https://prove2.me/theorems/93b01bb6-9c31-4c3b-9840-4002eadccd2a
-- title:
--   PW: GAe comp
-- statement:
--   The PW construction uses the GAe comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeightCompApply.lean#L127-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeightCompApply.lean#L127-L128

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

theorem Formalism.InvariantFactorPaths.PW.GAe_comp (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r) (μ : Fin n → ℤ) :
    (GAe p LL j e).comp μ = weightedHomogeneousComponent (fun x => (wv LL j x) ∘ e) μ := by sorry
