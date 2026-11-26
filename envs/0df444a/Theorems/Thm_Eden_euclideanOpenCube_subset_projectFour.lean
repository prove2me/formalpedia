-- Prove2me | Theorems.Thm_Eden_euclideanOpenCube_subset_projectFour
-- name    : Eden.euclideanOpenCube_subset_projectFour
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:09:14.556849+00:00
-- url     : https://prove2.me/theorems/5d75a1fc-4197-4a8c-9ec1-0c1e63a25901
-- title:
--   Eden: euclidean Open Cube subset project Four
-- statement:
--   The Eden construction uses the euclidean Open Cube subset project Four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/HausdorffGeometry.lean#L82-L85
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/HausdorffGeometry.lean#L82-L85

import Definitions.Def_Eden_TorusAngles
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Definitions.Def_Eden_HausdorffGeometry
set_option autoImplicit true
noncomputable section
open Set MeasureTheory
open Eden

theorem Eden.euclideanOpenCube_subset_projectFour :
    euclideanOpenCube 4 ⊆ projectFour '' attractor := by sorry
