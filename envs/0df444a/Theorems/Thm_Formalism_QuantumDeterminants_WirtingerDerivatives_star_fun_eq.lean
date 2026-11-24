-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_star_fun_eq
-- name    : Formalism.QuantumDeterminants.WirtingerDerivatives.star_fun_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:18:40.438847+00:00
-- url     : https://prove2.me/theorems/e2704253-c26a-4d06-9f20-93ce6de53b91
-- title:
--   Wirtinger Derivatives: star fun eq
-- statement:
--   The Wirtinger Derivatives construction uses the star fun eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L174-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L174-L176

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

theorem Formalism.QuantumDeterminants.WirtingerDerivatives.star_fun_eq (k : Fin m) :
    (fun y : Fin m → ℂ => star (y k)) = fun y => (Complex.conjCLE : ℂ →L[ℝ] ℂ) (y k) := by sorry
