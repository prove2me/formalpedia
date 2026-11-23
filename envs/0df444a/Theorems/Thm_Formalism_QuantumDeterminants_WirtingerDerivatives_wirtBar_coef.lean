-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_wirtBar_coef
-- name    : Formalism.QuantumDeterminants.WirtingerDerivatives.wirtBar_coef
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:41:33.301056+00:00
-- url     : https://prove2.me/theorems/423eb9c5-fdce-4aa2-abd0-82e88339746c
-- title:
--   Wirtinger Derivatives: wirt Bar coef
-- statement:
--   The Wirtinger Derivatives construction uses the wirt Bar coef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L226-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L226-L237

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

theorem Formalism.QuantumDeterminants.WirtingerDerivatives.wirtBar_coef {k : Fin m} {x : Fin m → ℂ} (hx : x ∈ OmX m) (l : Fin m) (j : Fin 6) :
    wirtBar l (coef k j) x = if ¬ (j : ℕ) < 3 ∧ l = k then ck k j x else 0 := by sorry
