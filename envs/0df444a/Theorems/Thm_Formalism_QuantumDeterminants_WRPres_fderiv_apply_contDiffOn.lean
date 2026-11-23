-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_WRPres_fderiv_apply_contDiffOn
-- name    : Formalism.QuantumDeterminants.WRPres.fderiv_apply_contDiffOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:04:02.937245+00:00
-- url     : https://prove2.me/theorems/0df51ec6-2aaf-4c5a-a2ba-f3f76b4b74ba
-- title:
--   WRPres: fderiv apply cont Diff On
-- statement:
--   The WRPres construction uses the fderiv apply cont Diff On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRPres.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/WRPres.lean#L25-L27

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

theorem Formalism.QuantumDeterminants.WRPres.fderiv_apply_contDiffOn {f : (Fin m → ℂ) → E} (hf : ContDiffOn ℝ ∞ f (OmX m))
    (v : Fin m → ℂ) : ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x v) (OmX m) := by sorry
