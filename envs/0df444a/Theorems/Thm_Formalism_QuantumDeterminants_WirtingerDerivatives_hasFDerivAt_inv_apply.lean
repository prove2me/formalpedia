-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_hasFDerivAt_inv_apply
-- name    : Formalism.QuantumDeterminants.WirtingerDerivatives.hasFDerivAt_inv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:24.693188+00:00
-- url     : https://prove2.me/theorems/6e28eb31-d990-4631-9f50-c997b48df9f0
-- title:
--   Wirtinger Derivatives: has FDeriv At inv apply
-- statement:
--   The Wirtinger Derivatives construction uses the has FDeriv At inv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L58-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L58-L63

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open Filter
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WirtingerDerivatives
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.QuantumDeterminants.WirtingerDerivatives.hasFDerivAt_inv_apply (k : Fin m) {x : Fin m → ℂ} (hx : x k ≠ 0) :
    HasFDerivAt (fun y : Fin m → ℂ => (y k)⁻¹)
      (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(x k ^ 2)⁻¹)).restrictScalars ℝ).comp
        (ContinuousLinearMap.proj k)) x := by sorry
