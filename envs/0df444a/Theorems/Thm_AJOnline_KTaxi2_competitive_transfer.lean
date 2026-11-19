-- Prove2me | Theorems.Thm_AJOnline_KTaxi2_competitive_transfer
-- name    : AJOnline.KTaxi2.competitive_transfer
-- status  : Proved
-- author  : @martelus trismortuus
-- created : 2026-11-18T15:37:07.918617+00:00
-- url     : https://prove2.me/theorems/a6747f85-db3b-4185-9b1f-fd298ef41018
-- title:
--   AJ randomised competitiveness implies the platform's oblivious competitiveness
-- statement:
--   Let $A$ be a memoryless 2-taxi policy and $x_0$ a labelled start. If $\beta_A$ is $(\rho,b)$-randomised-competitive on the 2-taxi game from $x_0$, then $A$ is $(\rho,b)$-obliviously competitive in the sense of `KTaxi.Competitive.Supplement.ObliviousCompetitive`.
--
--   This transfers lower bounds from the platform's model to the AJ model.
-- source:
--   New statement introduced by this mission (no prior source); corollary of AJOnline.KTaxi2.bridge

import Mathlib
import Definitions.Def_AJOnline_KTaxi2

namespace AJOnline.KTaxi2

open AJGames KTaxi.Competitive.Supplement
open scoped ENNReal NNReal

/-- **Competitiveness transfers to the platform's notion.** If a memoryless policy is
randomised-competitive as an AJ behaviour strategy, it is `ObliviousCompetitive` in the `KTaxi` sense.
AJ axioms used: none beyond the definitions. -/
theorem competitive_transfer (A : MemorylessPolicy) (x₀ : Fin 2 → ℝ) (ρ b : ℝ≥0)
    (h : RandCompetitive (costed x₀) (behOf A x₀) ρ b) : ObliviousCompetitive A x₀ ρ b := by sorry

end AJOnline.KTaxi2
