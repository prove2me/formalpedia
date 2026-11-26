-- Prove2me | Theorems.Thm_Eden_kaplanYorkeDimension_radiusPair_bound_and_eq
-- name    : Eden.kaplanYorkeDimension_radiusPair_bound_and_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:51:19.326519+00:00
-- url     : https://prove2.me/theorems/1eebcd0e-3177-4124-b8b8-e8071ce447d4
-- title:
--   Eden: kaplan Yorke Dimension radius Pair bound and eq
-- statement:
--   Exhausting the three possible limiting squared radii gives the sharp
--   bound and its unique radius pair, allowing either order of the planes.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionTable.lean#L86-L103
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DimensionTable.lean#L86-L103

import Definitions.Def_Eden_SpectrumTable
import Definitions.Def_Eden_FiniteTimeDimension
import Definitions.Def_Eden_DimensionTable
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.kaplanYorkeDimension_radiusPair_bound_and_eq {c s₁ s₂ : ℝ} (hc : 4 < c)
    (hs₁ : s₁ = 0 ∨ s₁ = 1 ∨ s₁ = 2) (hs₂ : s₂ = 0 ∨ s₂ = 1 ∨ s₂ = 2) :
    kaplanYorkeDimension (descending (radiusPairSpectrum c s₁ s₂)) ≤ targetDimension c ∧
      (kaplanYorkeDimension (descending (radiusPairSpectrum c s₁ s₂)) = targetDimension c ↔
        s₁ = 1 ∧ s₂ = 1) := by sorry
