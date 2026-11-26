-- Prove2me | Theorems.Thm_Eden_norm_fderiv_evolution_radialBasis
-- name    : Eden.norm_fderiv_evolution_radialBasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:12:01.33006+00:00
-- url     : https://prove2.me/theorems/ccc8cebb-1680-5704-88e3-42646b14ebbb
-- title:
--   Eden: norm fderiv evolution radial Basis
-- statement:
--   The Eden construction uses the norm fderiv evolution radial Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/TorusDirections.lean#L44-L51
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/TorusDirections.lean#L44-L51

import Definitions.Def_Eden_StationaryFactors
import Definitions.Def_Eden_ExponentSums
import Definitions.Def_Eden_HausdorffDimensions
import Definitions.Def_Eden_TorusDirections
set_option autoImplicit true
noncomputable section
open Set Filter Topology MeasureTheory
open Eden

theorem Eden.norm_fderiv_evolution_radialBasis (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) (i : Fin 5) :
    ‖fderiv ℝ (evolution c t) p (radialOrthonormalBasis p i)‖ = derivativeFactors c t p i := by sorry
