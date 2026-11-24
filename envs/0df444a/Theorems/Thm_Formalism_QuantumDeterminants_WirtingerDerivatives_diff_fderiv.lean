-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_diff_fderiv
-- name    : Formalism.QuantumDeterminants.WirtingerDerivatives.diff_fderiv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:18:43.900843+00:00
-- url     : https://prove2.me/theorems/d2c7ab36-ebaf-4dd1-b524-cf1f14ca48c4
-- title:
--   Wirtinger Derivatives: diff fderiv
-- statement:
--   The Wirtinger Derivatives construction uses the diff fderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L75-L77

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

theorem Formalism.QuantumDeterminants.WirtingerDerivatives.diff_fderiv {g : (Fin m → ℂ) → E} {x : Fin m → ℂ} (hg : ContDiffAt ℝ ∞ g x) :
    DifferentiableAt ℝ (fderiv ℝ g) x := by sorry
