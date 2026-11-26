-- Prove2me | Theorems.Thm_Eden_attractor_subset_range_embedFour
-- name    : Eden.attractor_subset_range_embedFour
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:09:14.275194+00:00
-- url     : https://prove2.me/theorems/a0f54f66-d97d-40e5-9da8-c8d33f687be0
-- title:
--   Eden: attractor subset range embed Four
-- statement:
--   The Eden construction uses the attractor subset range embed Four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/HausdorffGeometry.lean#L70-L72
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/HausdorffGeometry.lean#L70-L72

import Definitions.Def_Eden_TorusAngles
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Definitions.Def_Eden_HausdorffGeometry
set_option autoImplicit true
noncomputable section
open Set MeasureTheory
open Eden

theorem Eden.attractor_subset_range_embedFour : attractor ⊆ range embedFour := by sorry
