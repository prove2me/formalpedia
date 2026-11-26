-- Prove2me | Theorems.Thm_Eden_projectFour_embedFour
-- name    : Eden.projectFour_embedFour
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:08:57.306399+00:00
-- url     : https://prove2.me/theorems/5f93384e-d3dc-5972-8cec-3f74484ea79d
-- title:
--   Eden: project Four embed Four
-- statement:
--   The Eden construction uses the project Four embed Four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/HausdorffGeometry.lean#L60-L63
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/HausdorffGeometry.lean#L60-L63

import Definitions.Def_Eden_TorusAngles
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Definitions.Def_Eden_HausdorffGeometry
set_option autoImplicit true
noncomputable section
open Set MeasureTheory
open Eden

theorem Eden.projectFour_embedFour (x : EuclideanSpace ℝ (Fin 4)) :
    projectFour (embedFour x) = x := by sorry
