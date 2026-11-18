-- Prove2me | solution 1 for lowerSum_le_upperSum_any
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:33:47.780882+00:00
-- url     : https://prove2.me/submissions/cac5f7cd-4d54-4e11-b502-87de250b75bf

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F009
import Mathlib.Tactic
import Theorems.Thm_DarbouxRS_lowerSum_le_upperSum_core
import Theorems.Thm_exists_common_refinement
import Theorems.Thm_lowerSum_le_of_refinement
import Theorems.Thm_upperSum_le_of_refinement
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open DarbouxRS
open scoped BigOperators Pointwise
noncomputable section

theorem solution {a b : ℝ} {f α : ℝ → ℝ}
    (hs : SourceHypotheses a b f α) (P1 P2 : Partition a b) :
    lowerSum P1 f α ≤ upperSum P2 f α := by
  rcases exists_common_refinement P1 P2 with ⟨Q, R1, R2, _⟩

  have h1 : lowerSum P1 f α ≤ lowerSum Q f α :=
    lowerSum_le_of_refinement hs R1

  have h2 : lowerSum Q f α ≤ upperSum Q f α :=
    DarbouxRS.lowerSum_le_upperSum_core Q hs

  have h3 : upperSum Q f α ≤ upperSum P2 f α :=
    upperSum_le_of_refinement hs R2

  exact le_trans h1 (le_trans h2 h3)
