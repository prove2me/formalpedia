-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_divPow_mul
-- name    : Formalism.InvariantFactorPaths.PW.divPow_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:52.767533+00:00
-- url     : https://prove2.me/theorems/73586cfd-2bb1-48d7-b9b3-b033a97a0d46
-- title:
--   PW: div Pow mul
-- statement:
--   The PW construction uses the div Pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L162-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/FischerAdjointnessHolds.lean#L162-L196

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
variable {K A : Type} [Field K] [CharZero K] [CommRing A] [Algebra K A]

theorem Formalism.InvariantFactorPaths.PW.divPow_mul (D : A →ₗ[K] A) (hD : ∀ a b, D (a * b) = a * D b + b * D a) (k : ℕ) (f g : A) :
    ((k.factorial : K))⁻¹ • (D ^ k) (f * g) =
      ∑ ij ∈ antidiagonal k, (((ij.1.factorial : K))⁻¹ • (D ^ ij.1) f) * (((ij.2.factorial : K))⁻¹ • (D ^ ij.2) g) := by sorry
