-- Prove2me | Theorems.Thm_Formalism_HF_P_apld_summable
-- name    : Formalism.HF.P.apld_summable
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:23:39.314983+00:00
-- url     : https://prove2.me/theorems/c2aade59-0848-4981-8600-a1e9f15e4b9d
-- title:
--   P: apld summable
-- statement:
--   The P construction uses the apld summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/APLogDensity.lean#L39-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/APLogDensity.lean#L39-L49

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

theorem Formalism.HF.P.apld_summable (a : ZMod q) {x : ℝ} (hx : 1 < x) :
    Summable fun n : ℕ ↦ residueClass a n / (n : ℝ) ^ x := by sorry
