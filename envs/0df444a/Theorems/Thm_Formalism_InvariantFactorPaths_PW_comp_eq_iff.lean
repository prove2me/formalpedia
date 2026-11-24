-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_comp_eq_iff
-- name    : Formalism.InvariantFactorPaths.PW.comp_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:44.791966+00:00
-- url     : https://prove2.me/theorems/3ab3488e-8522-4aac-8014-7418883a9ca9
-- title:
--   PW: comp eq iff
-- statement:
--   The PW construction uses the comp eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeightCompApply.lean#L220-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeightCompApply.lean#L220-L228

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

theorem Formalism.InvariantFactorPaths.PW.comp_eq_iff (Cs : Finset (Fin r)) (la la' : Fin r → ℤ) :
    la ∘ enumC Cs = la' ∘ enumC Cs ↔ ∀ c ∈ Cs, la c = la' c := by sorry
