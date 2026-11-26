-- Prove2me | Theorems.Thm_Eden_evolution_image_outerRadialRegion
-- name    : Eden.evolution_image_outerRadialRegion
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:44:30.673359+00:00
-- url     : https://prove2.me/theorems/aeabbb98-8ca7-4a23-82dd-1925e8a5c2c0
-- title:
--   Eden: evolution image outer Radial Region
-- statement:
--   The Eden construction uses the evolution image outer Radial Region property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L99-L101
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L99-L101

import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_Nontransitivity
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.evolution_image_outerRadialRegion (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    evolution c t '' outerRadialRegion = outerRadialRegion := by sorry
