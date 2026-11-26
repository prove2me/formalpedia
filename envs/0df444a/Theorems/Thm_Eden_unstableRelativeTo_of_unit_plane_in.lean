-- Prove2me | Theorems.Thm_Eden_unstableRelativeTo_of_unit_plane_in
-- name    : Eden.unstableRelativeTo_of_unit_plane_in
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:27:33.811048+00:00
-- url     : https://prove2.me/theorems/c16e7575-f3cf-533b-80b5-747c0783ff96
-- title:
--   Eden: unstable Relative To of unit plane in
-- statement:
--   A set of unit planar radius is unstable if it contains the indicated radial
--   endpoint.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/NonlinearInstability.lean#L25-L54
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/NonlinearInstability.lean#L25-L54

import Definitions.Def_Eden_InstabilityGeometry
import Definitions.Def_Eden_NonlinearInstability
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.unstableRelativeTo_of_unit_plane_in (c : ℝ) (j : Fin 2) {B K : Set PhaseSpace}
    {s : ℝ} (hB : ∀ r ∈ Icc (0 : ℝ) 1, radialPerturbation j r s ∈ B)
    (hend : radialPerturbation j 1 s ∈ K)
    (hunit : ∀ q ∈ K, ‖planeProjection j q‖ = 1) :
    UnstableRelativeTo c B K := by sorry
