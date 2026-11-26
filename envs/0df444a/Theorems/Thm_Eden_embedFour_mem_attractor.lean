-- Prove2me | Theorems.Thm_Eden_embedFour_mem_attractor
-- name    : Eden.embedFour_mem_attractor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:09:18.124728+00:00
-- url     : https://prove2.me/theorems/109d4fcc-cf93-421e-a35c-10b6cdcb3216
-- title:
--   Eden: embed Four mem attractor
-- statement:
--   The Eden construction uses the embed Four mem attractor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/HausdorffGeometry.lean#L74-L80
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/HausdorffGeometry.lean#L74-L80

import Definitions.Def_Eden_TorusAngles
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Definitions.Def_Eden_HausdorffGeometry
set_option autoImplicit true
noncomputable section
open Set MeasureTheory
open Eden

theorem Eden.embedFour_mem_attractor {x : EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ euclideanOpenCube 4) : embedFour x ∈ attractor := by sorry
