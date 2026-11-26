-- Prove2me | Theorems.Thm_Eden_squaredRadiusEvolution_surjOn
-- name    : Eden.squaredRadiusEvolution_surjOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:09:05.35982+00:00
-- url     : https://prove2.me/theorems/34edf81f-9d2a-446a-8b3b-07cbc3f90cc0
-- title:
--   Eden: squared Radius Evolution surj On
-- statement:
--   The Eden construction uses the squared Radius Evolution surj On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/StrictInvariance.lean#L16-L24
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/StrictInvariance.lean#L16-L24

import Definitions.Def_Eden_InvariantSets
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_Eden_StrictInvariance
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.squaredRadiusEvolution_surjOn {t : ℝ} (ht : 0 ≤ t) :
    Set.SurjOn (squaredRadiusEvolution t) (Set.Icc 0 2) (Set.Icc 0 2) := by sorry
