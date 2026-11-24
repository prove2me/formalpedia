-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_LatticeBasis_exists_family
-- name    : Formalism.InvariantFactorPaths.PW.LatticeBasis.exists_family
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:10.936351+00:00
-- url     : https://prove2.me/theorems/07c9c1d4-5175-4cf3-bda4-c078024fa82f
-- title:
--   Lattice Basis: exists family
-- statement:
--   The Lattice Basis construction uses the exists family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/LatticeBasisPolynomial.lean#L46-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/LatticeBasisPolynomial.lean#L46-L107

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

theorem Formalism.InvariantFactorPaths.PW.LatticeBasis.exists_family (d : ℕ) : ∀ (U : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])), FiniteDimensional ℚ_[p] U →
    Module.finrank ℚ_[p] U = d →
    ∃ (k : ℕ) (b : Fin k → MvPolynomial σ ℚ_[p]), LinearIndependent ℚ_[p] b ∧
      Submodule.span ℚ_[p] (Set.range b) = U ∧ (∀ i, b i ∈ IntPol p σ) ∧
      ∀ x ∈ U, x ∈ IntPol p σ → ∃ c : Fin k → ℚ_[p], (∀ i, ‖c i‖ ≤ 1) ∧ x = ∑ i, c i • b i := by sorry
