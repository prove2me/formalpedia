-- Prove2me | Theorems.Thm_Formalism_HF_P_hasDerivAt_F
-- name    : Formalism.HF.P.hasDerivAt_F
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:24:21.833336+00:00
-- url     : https://prove2.me/theorems/8784c7b1-3717-4961-a3a6-422630fc869c
-- title:
--   P: has Deriv At F
-- statement:
--   The P construction uses the has Deriv At F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/LogToDir.lean#L57-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/LogToDir.lean#L57-L81

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

theorem Formalism.HF.P.hasDerivAt_F (S : Set ℕ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun x : ℝ => ∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ S}.indicator
        (fun m : ℕ => 1 / (m : ℝ) ^ x) n)
      (-∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ S}.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n)
      x := by sorry
