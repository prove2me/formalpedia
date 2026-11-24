-- Prove2me | Theorems.Thm_Formalism_HF_P_apld_prime_part_eq
-- name    : Formalism.HF.P.apld_prime_part_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:23:41.373847+00:00
-- url     : https://prove2.me/theorems/1d1b9e9b-6b2c-4392-962b-1db95fe6f126
-- title:
--   P: apld prime part eq
-- statement:
--   The P construction uses the apld prime part eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/APLogDensity.lean#L84-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/APLogDensity.lean#L84-L97

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_APLogDensity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology ArithmeticFunction ArithmeticFunction.vonMangoldt Complex LSeries
noncomputable section
open Formalism Formalism.HF Formalism.HF.P
variable {q : ℕ} [NeZero q] {a : ZMod q}

theorem Formalism.HF.P.apld_prime_part_eq (a : ZMod q) (x : ℝ) (n : ℕ) :
    (if n.Prime then residueClass a n else 0) / (n : ℝ) ^ x =
      {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod q) = a}}.indicator
        (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n := by sorry
