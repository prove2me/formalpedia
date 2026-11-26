-- Prove2me | Theorems.Thm_Eden_hasDerivAt_planarMovingPerturbation
-- name    : Eden.hasDerivAt_planarMovingPerturbation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:31:18.486109+00:00
-- url     : https://prove2.me/theorems/d7dbede0-5675-4934-b768-60115a2e09d1
-- title:
--   Eden: has Deriv At planar Moving Perturbation
-- statement:
--   The two components of a variation obey xi'=a(s)xi and eta'=b(s)eta in the moving
--   orthonormal frame, at every positive time.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarMovingFrame.lean#L65-L72
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PlanarMovingFrame.lean#L65-L72

import Definitions.Def_Eden_PlanarDerivative
import Definitions.Def_Eden_PlanarMovingFrame
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.hasDerivAt_planarMovingPerturbation (Ω : ℝ) {t : ℝ} (ht : 0 < t)
    (p v : PlanarSpace) :
    HasDerivAt (fun τ => planarMovingPerturbation Ω τ p v)
      (!₂[radialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 0,
        tangentialRate (planarEvolution Ω t p 0 ^ 2 + planarEvolution Ω t p 1 ^ 2) *
          planarMovingPerturbation Ω t p v 1]) t := by sorry
