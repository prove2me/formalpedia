-- Prove2me | Theorems.Thm_Eden_embedFour_projectFour
-- name    : Eden.embedFour_projectFour
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:09:05.297028+00:00
-- url     : https://prove2.me/theorems/a20cd4e2-22f5-4e8b-ae5e-92d8114d4210
-- title:
--   Eden: embed Four project Four
-- statement:
--   The Eden construction uses the embed Four project Four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/HausdorffGeometry.lean#L65-L68
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/HausdorffGeometry.lean#L65-L68

import Definitions.Def_Eden_TorusAngles
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Definitions.Def_Eden_HausdorffGeometry
set_option autoImplicit true
noncomputable section
open Set MeasureTheory
open Eden

theorem Eden.embedFour_projectFour {p : PhaseSpace} (hp : p 4 = 0) :
    embedFour (projectFour p) = p := by sorry
