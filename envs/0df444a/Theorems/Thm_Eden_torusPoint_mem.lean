-- Prove2me | Theorems.Thm_Eden_torusPoint_mem
-- name    : Eden.torusPoint_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:00:58.123676+00:00
-- url     : https://prove2.me/theorems/3760dfc7-69d3-484a-9661-809b8d692135
-- title:
--   Eden: torus Point mem
-- statement:
--   The Eden construction uses the torus Point mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/TorusAngles.lean#L19-L20
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/TorusAngles.lean#L19-L20

import Definitions.Def_Eden_CircleOrbits
import Definitions.Def_Eden_TorusAngles
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.torusPoint_mem (θ₁ θ₂ : ℝ) : torusPoint θ₁ θ₂ ∈ torus := by sorry
