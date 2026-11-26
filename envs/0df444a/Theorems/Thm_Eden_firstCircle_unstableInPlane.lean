-- Prove2me | Theorems.Thm_Eden_firstCircle_unstableInPlane
-- name    : Eden.firstCircle_unstableInPlane
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:59:49.935489+00:00
-- url     : https://prove2.me/theorems/fd169ffa-56b2-59a8-b4a3-1881dcce2236
-- title:
--   Eden: first Circle unstable In Plane
-- statement:
--   Instability of the first circle with perturbations in its own planar subsystem.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/NonlinearInstability.lean#L72-L80
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/NonlinearInstability.lean#L72-L80

import Definitions.Def_Eden_InstabilityGeometry
import Definitions.Def_Eden_NonlinearInstability
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.firstCircle_unstableInPlane (c : ℝ) :
    UnstableRelativeTo c (attractor ∩ coordinatePlane 0) (firstCircle 1) := by sorry
