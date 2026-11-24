-- Prove2me | Theorems.Thm_Formalism_HF_P_summable_F
-- name    : Formalism.HF.P.summable_F
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:23:42.751789+00:00
-- url     : https://prove2.me/theorems/0f14c199-712c-4d0d-95b4-4472e5d1dd42
-- title:
--   P: summable F
-- statement:
--   The P construction uses the summable F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/LogToDir.lean#L50-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/LogToDir.lean#L50-L55

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

theorem Formalism.HF.P.summable_F (S : Set ℕ) {x : ℝ} (hx : 1 < x) :
    Summable (fun n : ℕ => {p : ℕ | p.Prime ∧ p ∈ S}.indicator (fun m : ℕ => 1 / (m : ℝ) ^ x) n) := by sorry
