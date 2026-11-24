-- Prove2me | Theorems.Thm_Formalism_HF_P_summable_log_div_rpow
-- name    : Formalism.HF.P.summable_log_div_rpow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:24:05.772409+00:00
-- url     : https://prove2.me/theorems/046ac80f-8808-48ee-8e58-23e3ace23c06
-- title:
--   P: summable log div rpow
-- statement:
--   The P construction uses the summable log div rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/LogToDir.lean#L13-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/LogToDir.lean#L13-L30

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_LogToDir
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open Formalism Formalism.HF Formalism.HF.P

theorem Formalism.HF.P.summable_log_div_rpow {y : ℝ} (hy : 1 < y) :
    Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ y) := by sorry
