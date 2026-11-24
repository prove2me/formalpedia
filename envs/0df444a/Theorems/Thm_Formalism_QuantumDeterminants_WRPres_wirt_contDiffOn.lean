-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WRPres_wirt_contDiffOn
-- name    : Formalism.QuantumDeterminants.WRPres.wirt_contDiffOn
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:18:35.392694+00:00
-- url     : https://prove2.me/theorems/7e86c078-9fab-4a65-b746-e539add562bf
-- title:
--   WRPres: wirt cont Diff On
-- statement:
--   The WRPres construction uses the wirt cont Diff On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRPres.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRPres.lean#L29-L32

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRPres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WRPres
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.QuantumDeterminants.WRPres.wirt_contDiffOn {f : (Fin m → ℂ) → E} (hf : ContDiffOn ℝ ∞ f (OmX m)) (l : Fin m) :
    ContDiffOn ℝ ∞ (wirt l f) (OmX m) := by sorry
