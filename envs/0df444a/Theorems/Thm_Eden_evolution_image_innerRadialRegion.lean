-- Prove2me | Theorems.Thm_Eden_evolution_image_innerRadialRegion
-- name    : Eden.evolution_image_innerRadialRegion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:08:24.118468+00:00
-- url     : https://prove2.me/theorems/33947285-45ca-5854-bc23-fc8047a9c32b
-- title:
--   Eden: evolution image inner Radial Region
-- statement:
--   The Eden construction uses the evolution image inner Radial Region property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L95-L97
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L95-L97

import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_Nontransitivity
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.evolution_image_innerRadialRegion (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    evolution c t '' innerRadialRegion = innerRadialRegion := by sorry
