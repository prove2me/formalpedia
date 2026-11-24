-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_LatticeBasis_mem_intPol_iff
-- name    : Formalism.InvariantFactorPaths.PW.LatticeBasis.mem_intPol_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:13.994346+00:00
-- url     : https://prove2.me/theorems/247dfc0a-5915-4b20-99b6-f4bfe62e118f
-- title:
--   Lattice Basis: mem int Pol iff
-- statement:
--   The Lattice Basis construction uses the mem int Pol iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/LatticeBasisPolynomial.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/LatticeBasisPolynomial.lean#L11-L23

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatticeBasisPolynomial
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
open Formalism.InvariantFactorPaths.PW.LatticeBasis
variable {p : ℕ} [Fact p.Prime] {σ : Type}

theorem Formalism.InvariantFactorPaths.PW.LatticeBasis.mem_intPol_iff (x : MvPolynomial σ ℚ_[p]) : x ∈ IntPol p σ ↔ ∀ m, ‖x.coeff m‖ ≤ 1 := by sorry
