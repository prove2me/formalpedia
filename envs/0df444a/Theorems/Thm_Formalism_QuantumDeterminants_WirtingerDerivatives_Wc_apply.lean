-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_Wc_apply
-- name    : Formalism.QuantumDeterminants.WirtingerDerivatives.Wc_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:18:18.297381+00:00
-- url     : https://prove2.me/theorems/b58545a3-4c7a-4aa5-b93a-65baa1f8aa24
-- title:
--   Wirtinger Derivatives: Wc apply
-- statement:
--   The Wirtinger Derivatives construction uses the Wc apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L40-L42

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

theorem Formalism.QuantumDeterminants.WirtingerDerivatives.Wc_apply (u w : Fin m → ℂ) (s : ℂ) (T : (Fin m → ℂ) →L[ℝ] E) :
    Wc u w s T = (1 / 2 : ℂ) • (T u + s • T w) := by sorry
