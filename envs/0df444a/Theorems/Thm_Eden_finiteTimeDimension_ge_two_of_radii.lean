-- Prove2me | Theorems.Thm_Eden_finiteTimeDimension_ge_two_of_radii
-- name    : Eden.finiteTimeDimension_ge_two_of_radii
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:59:34.558895+00:00
-- url     : https://prove2.me/theorems/858abc30-b802-4467-b738-a5112e7b1872
-- title:
--   Eden: finite Time Dimension ge two of radii
-- statement:
--   The Eden construction uses the finite Time Dimension ge two of radii property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/NeutralDimensionBounds.lean#L81-L97
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/NeutralDimensionBounds.lean#L81-L97

import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_NeutralDimensionBounds
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.finiteTimeDimension_ge_two_of_radii (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor)
    (hs₁ : 1 ≤ radiusSq₁ p) (hs₂ : 1 ≤ radiusSq₂ p) :
    2 ≤ finiteTimeDimension c t p := by sorry
