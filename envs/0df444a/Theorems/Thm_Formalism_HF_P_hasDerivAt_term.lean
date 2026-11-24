-- Prove2me | Theorems.Thm_Formalism_HF_P_hasDerivAt_term
-- name    : Formalism.HF.P.hasDerivAt_term
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:23:51.197291+00:00
-- url     : https://prove2.me/theorems/f4d5ea69-d9e8-4107-9939-f32e41f845e4
-- title:
--   P: has Deriv At term
-- statement:
--   The P construction uses the has Deriv At term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/LogToDir.lean#L32-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/LogToDir.lean#L32-L48

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

theorem Formalism.HF.P.hasDerivAt_term (S : Set ℕ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => {p : ℕ | p.Prime ∧ p ∈ S}.indicator (fun m : ℕ => 1 / (m : ℝ) ^ x) n)
      (-{p : ℕ | p.Prime ∧ p ∈ S}.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n) x := by sorry
