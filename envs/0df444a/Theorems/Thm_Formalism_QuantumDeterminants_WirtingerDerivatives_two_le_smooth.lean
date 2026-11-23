-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_two_le_smooth
-- name    : Formalism.QuantumDeterminants.WirtingerDerivatives.two_le_smooth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:35.857392+00:00
-- url     : https://prove2.me/theorems/e4e0813e-4810-4ad0-bbcd-55808c673e0c
-- title:
--   Wirtinger Derivatives: two le smooth
-- statement:
--   The Wirtinger Derivatives construction uses the two le smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L27-L30

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

theorem Formalism.QuantumDeterminants.WirtingerDerivatives.two_le_smooth : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by sorry
