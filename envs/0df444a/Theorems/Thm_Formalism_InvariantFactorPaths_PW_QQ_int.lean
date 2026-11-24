-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_QQ_int
-- name    : Formalism.InvariantFactorPaths.PW.QQ_int
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:57.146813+00:00
-- url     : https://prove2.me/theorems/9560e095-1321-4ad7-8e79-9400c4e4776b
-- title:
--   PW: QQ int
-- statement:
--   The PW construction uses the QQ int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/TypeInt.lean#L356-L381
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/TypeInt.lean#L356-L381

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_TypeInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames
variable (p : ℕ) [Fact p.Prime] {U V : Type} [AddCommGroup U] [Module ℚ_[p] U] [AddCommGroup V] [Module ℚ_[p] V]
  {n : ℕ}

theorem Formalism.InvariantFactorPaths.PW.QQ_int (G₁ : GlW ℚ_[p] U n) (G₂ : GlW ℚ_[p] V n) (S : Finset (Fin n → ℤ)) (l : ℕ) {k : ℕ}
    (b : Module.Basis (Fin k) ℚ_[p] U) {L : AddSubgroup U} {M : AddSubgroup V} (hZ : ZpClosed p M)
    (hLd : DivStable G₁.E L) (hMd : DivStable G₂.E M) (hLg : ∀ μ, ∀ x ∈ L, G₁.comp μ x ∈ L)
    (hMg : ∀ μ, ∀ x ∈ M, G₂.comp μ x ∈ M) (hbL : ∀ i, b i ∈ L) (hbi : ∀ x ∈ L, ∀ i, ‖b.repr x i‖ ≤ 1)
    {m : V} (hm : m ∈ M) :
    ((p : ℚ_[p]) ^ (n.choose 2 * Nat.log p (l + n - 1))) • QQ G₁ G₂ S l b m ∈ M := by sorry
