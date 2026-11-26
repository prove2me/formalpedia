-- Prove2me | Theorems.Thm_EdenVerified_s07_torus_directions
-- name    : EdenVerified.s07_torus_directions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:22:42.238679+00:00
-- url     : https://prove2.me/theorems/07e03bd7-ffff-5f0d-816b-bb04aece715e
-- title:
--   Eden Verified: s07 torus directions
-- statement:
--   The orthonormal radial/tangential directions, in that order.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L257-L270
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L257-L270

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.s07_torus_directions (c : ℝ) (hc : 4 < c) (p : PhaseSpace) (hp : p ∈ torus) :
    (fun i => radialOrthonormalBasis p i) =
      ![!₂[p 0, p 1, 0, 0, 0], !₂[-p 1, p 0, 0, 0, 0],
        !₂[0, 0, p 2, p 3, 0], !₂[0, 0, -p 3, p 2, 0], !₂[0, 0, 0, 0, 1]] ∧
    (∀ t : ℝ, 0 ≤ t → ∀ i : Fin 5,
      ‖fderiv ℝ (evolution c t) p (radialOrthonormalBasis p i)‖ =
        Real.exp ((![2, 0, 2, 0, -c] : Fin 5 → ℝ) i*t)) ∧
    (∀ i : Fin 5, Tendsto (fun t : ℝ => Real.log
      ‖fderiv ℝ (evolution c t) p (radialOrthonormalBasis p i)‖ / t) atTop
      (𝓝 ((![2, 0, 2, 0, -c] : Fin 5 → ℝ) i))) ∧
    lyapunovExponent c p = ![2, 2, 0, 0, -c] ∧ 0 < (2 : ℝ) ∧ -c < 0 := by sorry
