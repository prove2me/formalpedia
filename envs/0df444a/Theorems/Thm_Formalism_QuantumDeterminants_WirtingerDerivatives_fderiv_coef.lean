-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_fderiv_coef
-- name    : Formalism.QuantumDeterminants.WirtingerDerivatives.fderiv_coef
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:09.530851+00:00
-- url     : https://prove2.me/theorems/58534778-098f-4f97-8562-08cffe6884e3
-- title:
--   Wirtinger Derivatives: fderiv coef
-- statement:
--   The Wirtinger Derivatives construction uses the fderiv coef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L178-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L178-L212

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

theorem Formalism.QuantumDeterminants.WirtingerDerivatives.fderiv_coef {k : Fin m} {x : Fin m → ℂ} (hx : x ∈ OmX m) (j : Fin 6) (v : Fin m → ℂ) :
    fderiv ℝ (coef k j) x v =
      if (j : ℕ) < 3 then ck k j x * v k else ck k j x * star (v k) := by sorry
