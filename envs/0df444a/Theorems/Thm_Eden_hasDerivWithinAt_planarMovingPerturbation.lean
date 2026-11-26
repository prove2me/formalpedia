-- Prove2me | Theorems.Thm_Eden_hasDerivWithinAt_planarMovingPerturbation
-- name    : Eden.hasDerivWithinAt_planarMovingPerturbation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:27:25.019596+00:00
-- url     : https://prove2.me/theorems/911dc1b4-bd05-4c63-baae-9fd2c24bc0c2
-- title:
--   Eden: has Deriv Within At planar Moving Perturbation
-- statement:
--   The right-sided variational equations include time zero and zero initial radius,
--   using the Cartesian input frame in the latter case.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarMovingFrame.lean#L33-L61
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarMovingFrame.lean#L33-L61

import Definitions.Def_Eden_PlanarDerivative
import Definitions.Def_Eden_PlanarMovingFrame
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.hasDerivWithinAt_planarMovingPerturbation (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p v : PlanarSpace) :
    HasDerivWithinAt (fun τ => planarMovingPerturbation Ω τ p v)
      (!₂[radialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 0,
        tangentialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 1]) (Set.Ici 0) t := by sorry
