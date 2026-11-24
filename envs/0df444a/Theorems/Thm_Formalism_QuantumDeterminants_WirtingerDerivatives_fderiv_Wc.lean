-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_fderiv_Wc
-- name    : Formalism.QuantumDeterminants.WirtingerDerivatives.fderiv_Wc
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:18:36.933002+00:00
-- url     : https://prove2.me/theorems/7dea8eb1-301f-4489-9c2c-6f210e9798ec
-- title:
--   Wirtinger Derivatives: fderiv Wc
-- statement:
--   The Wirtinger Derivatives construction uses the fderiv Wc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L83-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRWeyl.lean#L83-L86

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

theorem Formalism.QuantumDeterminants.WirtingerDerivatives.fderiv_Wc {g : (Fin m → ℂ) → E} {x : Fin m → ℂ} (hg : ContDiffAt ℝ ∞ g x)
    (u w : Fin m → ℂ) (s : ℂ) :
    fderiv ℝ (fun y => Wc u w s (fderiv ℝ g y)) x = (Wc u w s).comp (fderiv ℝ (fderiv ℝ g) x) := by sorry
