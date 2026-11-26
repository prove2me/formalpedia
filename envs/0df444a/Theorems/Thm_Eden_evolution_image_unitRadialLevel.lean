-- Prove2me | Theorems.Thm_Eden_evolution_image_unitRadialLevel
-- name    : Eden.evolution_image_unitRadialLevel
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:44:44.929924+00:00
-- url     : https://prove2.me/theorems/393aae69-0272-5522-a9cb-fd11e8c41006
-- title:
--   Eden: evolution image unit Radial Level
-- statement:
--   The Eden construction uses the evolution image unit Radial Level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L103-L105
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L103-L105

import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_Nontransitivity
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.evolution_image_unitRadialLevel (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    evolution c t '' unitRadialLevel = unitRadialLevel := by sorry
