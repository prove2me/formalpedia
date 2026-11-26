-- Prove2me | Theorems.Thm_Eden_stationary_radii_of_evolution_return
-- name    : Eden.stationary_radii_of_evolution_return
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:45:32.148403+00:00
-- url     : https://prove2.me/theorems/67f546d3-cb14-417c-8fd3-5c9e0b37f6f8
-- title:
--   Eden: stationary radii of evolution return
-- statement:
--   The Eden construction uses the stationary radii of evolution return property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialReturns.lean#L67-L75
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialReturns.lean#L67-L75

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_StationaryFactors
import Definitions.Def_Eden_RadialReturns
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.stationary_radii_of_evolution_return (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (h : evolution c t p = p) :
    (radiusSq₁ p = 0 ∨ radiusSq₁ p = 1 ∨ radiusSq₁ p = 2) ∧
    (radiusSq₂ p = 0 ∨ radiusSq₂ p = 1 ∨ radiusSq₂ p = 2) := by sorry
