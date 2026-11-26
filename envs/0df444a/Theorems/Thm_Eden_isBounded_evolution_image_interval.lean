-- Prove2me | Theorems.Thm_Eden_isBounded_evolution_image_interval
-- name    : Eden.isBounded_evolution_image_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:29:20.1292+00:00
-- url     : https://prove2.me/theorems/bf0b91b1-2fc4-5902-8867-bd83c73ca508
-- title:
--   Eden: is Bounded evolution image interval
-- statement:
--   The trajectory is bounded on every finite forward interval, including for real
--   parameters for which the fifth coordinate expands.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialQualitative.lean#L67-L70
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialQualitative.lean#L67-L70

import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_RadialQualitative
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden

theorem Eden.isBounded_evolution_image_interval (c T : ℝ) (p : PhaseSpace) :
    Bornology.IsBounded ((fun t => evolution c t p) '' Icc 0 T) := by sorry
