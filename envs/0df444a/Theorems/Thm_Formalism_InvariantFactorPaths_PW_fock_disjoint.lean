-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_fock_disjoint
-- name    : Formalism.InvariantFactorPaths.PW.fock_disjoint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:14.169271+00:00
-- url     : https://prove2.me/theorems/ac4aae96-b071-443c-8779-127150be1455
-- title:
--   PW: fock disjoint
-- statement:
--   The PW construction uses the fock disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L123-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L123-L127

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {σ : Type}

theorem Formalism.InvariantFactorPaths.PW.fock_disjoint (F G : MvPolynomial σ ℚ_[p]) (h : ∀ m ∈ F.support, m ∉ G.support) : fock p F G = 0 := by sorry
