-- Prove2me | Theorems.Thm_Formalism_HF_P_apld_nonprime_le
-- name    : Formalism.HF.P.apld_nonprime_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:23:37.561816+00:00
-- url     : https://prove2.me/theorems/b9fe6e4b-46e7-4210-b6ea-93357158af4e
-- title:
--   P: apld nonprime le
-- statement:
--   The P construction uses the apld nonprime le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/APLogDensity.lean#L73-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/APLogDensity.lean#L73-L82

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

theorem Formalism.HF.P.apld_nonprime_le (a : ZMod q) {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    (if n.Prime then 0 else residueClass a n) / (n : ℝ) ^ x ≤
      (if n.Prime then 0 else residueClass a n) / n := by sorry
