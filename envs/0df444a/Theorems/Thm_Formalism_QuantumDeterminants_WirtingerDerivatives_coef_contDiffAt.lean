-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_coef_contDiffAt
-- name    : Formalism.QuantumDeterminants.WirtingerDerivatives.coef_contDiffAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:41:41.140374+00:00
-- url     : https://prove2.me/theorems/cc775edd-5f56-4f81-ae3a-013930f9bb87
-- title:
--   Wirtinger Derivatives: coef cont Diff At
-- statement:
--   The Wirtinger Derivatives construction uses the coef cont Diff At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L244-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L244-L253

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

theorem Formalism.QuantumDeterminants.WirtingerDerivatives.coef_contDiffAt {k : Fin m} {x : Fin m → ℂ} (hx : x ∈ OmX m) (j : Fin 6) :
    ContDiffAt ℝ ∞ (coef k j) x := by sorry
