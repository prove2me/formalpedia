-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_Pstep_int
-- name    : Formalism.InvariantFactorPaths.PW.Pstep_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:09.139803+00:00
-- url     : https://prove2.me/theorems/f52d3995-ba24-4910-b65c-4e59d4a49f71
-- title:
--   PW: Pstep int
-- statement:
--   The PW construction uses the Pstep int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInt.lean#L133-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/InvInt.lean#L133-L145

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

theorem Formalism.InvariantFactorPaths.PW.Pstep_int {E : ι → ι → Module.End ℚ_[p] W} (hE : GlRel E) {M : AddSubgroup W} (hZ : ZpClosed p M)
    (hD : DivStable E M) {z : ι} {S : Finset ι} (hz : z ∉ S) (l : ℕ) {u : W} (hu : u ∈ M) :
    ((p : ℚ_[p]) ^ (S.card * Nat.log p (l + S.card))) • Pstep E S z l u ∈ M := by sorry
