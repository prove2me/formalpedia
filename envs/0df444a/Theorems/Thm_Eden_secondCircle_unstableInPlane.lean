-- Prove2me | Theorems.Thm_Eden_secondCircle_unstableInPlane
-- name    : Eden.secondCircle_unstableInPlane
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:00:38.461233+00:00
-- url     : https://prove2.me/theorems/b765a558-9b02-4723-895d-fcd1e924e574
-- title:
--   Eden: second Circle unstable In Plane
-- statement:
--   Instability of the second circle with perturbations in its own planar subsystem.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/NonlinearInstability.lean#L83-L91
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/NonlinearInstability.lean#L83-L91

import Definitions.Def_Eden_InstabilityGeometry
import Definitions.Def_Eden_NonlinearInstability
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.secondCircle_unstableInPlane (c : ℝ) :
    UnstableRelativeTo c (attractor ∩ coordinatePlane 1) (secondCircle 1) := by sorry
