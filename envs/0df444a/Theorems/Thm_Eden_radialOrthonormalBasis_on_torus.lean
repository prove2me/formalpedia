-- Prove2me | Theorems.Thm_Eden_radialOrthonormalBasis_on_torus
-- name    : Eden.radialOrthonormalBasis_on_torus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:52:40.703394+00:00
-- url     : https://prove2.me/theorems/5461b7be-64a0-5983-859e-959ddf6619ec
-- title:
--   Eden: radial Orthonormal Basis on torus
-- statement:
--   Explicit unit vectors in radial/tangential/radial/tangential/w order on T.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/TorusDirections.lean#L24-L33
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/TorusDirections.lean#L24-L33

import Definitions.Def_Eden_StationaryFactors
import Definitions.Def_Eden_ExponentSums
import Definitions.Def_Eden_HausdorffDimensions
import Definitions.Def_Eden_TorusDirections
set_option autoImplicit true
noncomputable section
open Set Filter Topology MeasureTheory
open Eden

theorem Eden.radialOrthonormalBasis_on_torus {p : PhaseSpace} (hp : p ∈ torus) :
    (fun i => radialOrthonormalBasis p i) =
      ![!₂[p 0, p 1, 0, 0, 0], !₂[-p 1, p 0, 0, 0, 0],
        !₂[0, 0, p 2, p 3, 0], !₂[0, 0, -p 3, p 2, 0], !₂[0, 0, 0, 0, 1]] := by sorry
