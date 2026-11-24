-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_Om_int
-- name    : Formalism.InvariantFactorPaths.PW.Om_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:53.389166+00:00
-- url     : https://prove2.me/theorems/eb4f0daf-05e1-4766-9841-e8dc1d94d3d7
-- title:
--   PW: Om int
-- statement:
--   The PW construction uses the Om int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInt.lean#L95-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInt.lean#L95-L131

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset
variable {p : ℕ} [Fact p.Prime]
variable {W ι : Type} [AddCommGroup W] [Module ℚ_[p] W] [DecidableEq ι]

theorem Formalism.InvariantFactorPaths.PW.Om_int {E : ι → ι → Module.End ℚ_[p] W} (hE : GlRel E) {M : AddSubgroup W} (hZ : ZpClosed p M)
    (hD : DivStable E M) (z : ι) (N : ℕ) (S : Finset ι) : z ∉ S → ∀ c q : ℕ, q + c ≤ N → ∀ u ∈ M,
      ((p : ℚ_[p]) ^ (S.card * Nat.log p N) *
        ((c.factorial : ℚ_[p]) / (((q + c).factorial : ℚ_[p]) * (q.factorial : ℚ_[p])))) • Om E S z q u ∈ M := by sorry
