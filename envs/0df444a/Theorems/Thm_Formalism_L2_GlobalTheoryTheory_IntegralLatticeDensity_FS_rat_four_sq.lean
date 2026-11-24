-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_rat_four_sq
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.rat_four_sq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:58:05.790802+00:00
-- url     : https://prove2.me/theorems/59b0417c-dfb0-4d95-a4b1-dfa0ae7b9085
-- title:
--   FS: rat four sq
-- statement:
--   The FS construction uses the rat four sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PFourSq.lean#L9-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PFourSq.lean#L9-L21

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.rat_four_sq (p : ℚ) (hp : 0 ≤ p) : ∃ a b c d : ℚ, p = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by sorry
