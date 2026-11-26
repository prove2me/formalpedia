-- Prove2me | Theorems.Thm_Eden_finiteTimeDimension_ge_one_of_first_radius
-- name    : Eden.finiteTimeDimension_ge_one_of_first_radius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:59:17.61558+00:00
-- url     : https://prove2.me/theorems/4c385ea3-393b-4b0d-aca7-2d6c8101c1d0
-- title:
--   Eden: finite Time Dimension ge one of first radius
-- statement:
--   The Eden construction uses the finite Time Dimension ge one of first radius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/NeutralDimensionBounds.lean#L69-L73
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/NeutralDimensionBounds.lean#L69-L73

import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_NeutralDimensionBounds
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.finiteTimeDimension_ge_one_of_first_radius (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor) (hs : 1 ≤ radiusSq₁ p) :
    1 ≤ finiteTimeDimension c t p := by sorry
