-- Prove2me | Theorems.Thm_Eden_radiusEvolution_mono
-- name    : Eden.radiusEvolution_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:10:51.463804+00:00
-- url     : https://prove2.me/theorems/4540d56e-539e-5807-96fb-c37866536c5b
-- title:
--   Eden: radius Evolution mono
-- statement:
--   The Eden construction uses the radius Evolution mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PhysicalRadius.lean#L46-L49
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PhysicalRadius.lean#L46-L49

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_PhysicalRadius
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden

theorem Eden.radiusEvolution_mono {t r R : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) (hrR : r ≤ R) :
    radiusEvolution t r ≤ radiusEvolution t R := by sorry
