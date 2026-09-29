-- Prove2me | Theorems.Thm_BraidsLinksMCG_extensionApproachRight_formula_child_v1
-- name    : BraidsLinksMCG.extensionApproachRight_formula_child_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-23T19:59:47.997269+00:00
-- url     : https://prove2.me/theorems/c091c82b-ffb1-48dc-8356-d5a7da2b5119
-- title:
--   The right edge of the strand-extension approach path matches the standard approach
-- statement:
--   At the right edge of the configuration-space square, the interpolating path is exactly the standard approach path after the final strand has been added.
-- source:
--   A theorem-only, pointwise formula isolating the right-edge coordinate identity used by the strand-extension boundary homotopy.

import Mathlib
import Definitions.Def_BraidsLinksMCG_StandardLoops
import Definitions.Def_TarchaBraids_HalfTwist

theorem BraidsLinksMCG.extensionApproachRight_formula_child_v1 (n : ℕ) (j : Fin n) (u : Set.Icc (0 : ℝ) 1) :
    ((1 - (u : ℝ) : ℝ) : ℂ) *
        TarchaBraids.twistPoint ((n : ℝ) + 3 / 2) 1 1 +
      ((u : ℝ) : ℂ) * ((((j : ℕ) : ℝ) + 3 / 2 : ℝ) : ℂ) +
      (((u : ℝ) * (1 - (u : ℝ)) : ℝ) : ℂ) * Complex.I =
      BraidsLinksMCG.approachFun n j (u : ℝ) := by sorry
