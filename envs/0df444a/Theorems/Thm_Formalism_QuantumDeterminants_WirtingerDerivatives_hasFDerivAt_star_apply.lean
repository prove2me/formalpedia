-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_hasFDerivAt_star_apply
-- name    : Formalism.QuantumDeterminants.WirtingerDerivatives.hasFDerivAt_star_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:18:37.663575+00:00
-- url     : https://prove2.me/theorems/400649c6-94db-43ca-82ee-e0caff866fa5
-- title:
--   Wirtinger Derivatives: has FDeriv At star apply
-- statement:
--   The Wirtinger Derivatives construction uses the has FDeriv At star apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L52-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L52-L56

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

theorem Formalism.QuantumDeterminants.WirtingerDerivatives.hasFDerivAt_star_apply (k : Fin m) (x : Fin m → ℂ) :
    HasFDerivAt (fun y : Fin m → ℂ => star (y k))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.proj k)) x := by sorry
