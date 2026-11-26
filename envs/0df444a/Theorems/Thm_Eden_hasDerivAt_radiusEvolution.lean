-- Prove2me | Theorems.Thm_Eden_hasDerivAt_radiusEvolution
-- name    : Eden.hasDerivAt_radiusEvolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:11:39.838795+00:00
-- url     : https://prove2.me/theorems/6d98630c-3b4b-4ec8-817b-059813a1102a
-- title:
--   Eden: has Deriv At radius Evolution
-- statement:
--   The Eden construction uses the has Deriv At radius Evolution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PhysicalRadius.lean#L64-L79
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PhysicalRadius.lean#L64-L79

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_PhysicalRadius
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden

theorem Eden.hasDerivAt_radiusEvolution {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) :
    HasDerivAt (fun τ => radiusEvolution τ r) (radialField (radiusEvolution t r)) t := by sorry
